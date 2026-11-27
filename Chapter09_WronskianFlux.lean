import Chapter08_StaticScattering
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

/-!
# 第九章　Wronskian流束の保存

## 主張と対象

第八章の静的な有限チャネル散乱方程式について、任意の解に対する流束保存と、
任意の複素入射・出射振幅に対する二次形式の恒等式を証明する。

    j(x) = Im(f†f') = (f†f' - (f')†f)/(2i)
    y = (f,f')
    J = [[0, -iI/2], [iI/2, 0]]
    B = [[0, I], [C, 0]],  C = M₀² + V - Ω²I

自己共役なCから B†J+JB=0 を導く。各層の指数作用素から構成した伝達行列と、
有限層全体の伝達行列について T†JT=J を証明する。
この証明にはCの正定値性を必要としない。

Jは自己共役だが不定であり、その二次形式が+1と-1を取る状態を実際に構成する。
従って、この保存則を通常の正定値内積に関するTのユニタリ性とは扱わない。

## 左右の振幅

第八章と同じ規約を使う。
左側：aL exp(+ikx) + bL exp(-ikx)。
右側：bR exp(+ik(x-W)) + aR exp(-ik(x-W))。

    K = diag(kα)
    jL = aL† K aL - bL† K bL
    jR = bR† K bR - aR† K aR

を任意の複素振幅に対して証明し、入射流束総和=出射流束総和へつなげる。
外部の基底は正規直交基底であり、干渉項の消失と平面波の絶対値1を実際に使う。
全外部チャネルが開く条件の下では、波数付き二乗和は非負で、ゼロなら振幅はゼロ。

## 接続点と証明範囲

第八章のIsScatteringSolutionを満たす任意のyに対して、全実数上の流束保存を証明する。
接続点では二階微分を要求せず、y=(f,f')の連続性を使う。
有限個の例外点を除いて微分がゼロである連続な実関数は定数、という補題を証明し、
これを流束に適用する。局所保存だけで全域保存を済ませたことにはしない。

境界の有限次元条件BoundaryMatchingからも、同じ入射・出射流束の等式を導く。
散乱解や散乱行列Sの存在・一意性、流束規格化後のSのユニタリティは、
第十章の課題であり、本章の仮定には含めない。

## 利用方法と検証環境

第一〜第八章と同じmathlibプロジェクトで使用する。
先行章のコンパイル済みモジュールを配置した後：

    lake env lean -DwarningAsError=true Chapter09_WronskianFlux.lean

Lean 4.24.0 / mathlib v4.24.0。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
末尾の #print axioms で主要定理の公理依存を確認する。
-/


noncomputable section
open scoped BigOperators ComplexOrder

namespace TwelveDimensionalPhaseSpace
namespace WronskianFlux
open Set StaticScattering

/-! ### 接続点をまたぐための実解析の補題 -/

theorem real_constant_interval (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : f a = f b := by
  rcases eq_or_lt_of_le hab with he | hab
  · exact congrArg f he
  · obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hab hf.continuousOn hd
    have heq := (eq_div_iff (sub_ne_zero.mpr hab.ne')).mp he
    linarith

theorem real_constant_interval_off_finset (S : Finset ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ x ∈ Ioo a b, x ∉ S → HasDerivAt f 0 x) : f a = f b := by
  induction S using Finset.induction_on generalizing a b with
  | empty =>
    exact real_constant_interval f hf a b hab (fun x hx => hd x hx (by simp))
  | @insert c S hc ih =>
    by_cases hin : c ∈ Ioo a b
    · have hleft : f a = f c := by
        apply ih a c hin.1.le
        intro x hx hxS
        apply hd x ⟨hx.1, lt_trans hx.2 hin.2⟩
        intro hm
        rcases Finset.mem_insert.mp hm with he | hm
        · exact (ne_of_lt hx.2) he
        · exact hxS hm
      have hright : f c = f b := by
        apply ih c b hin.2.le
        intro x hx hxS
        apply hd x ⟨lt_trans hin.1 hx.1, hx.2⟩
        intro hm
        rcases Finset.mem_insert.mp hm with he | hm
        · exact (ne_of_gt hx.1) he
        · exact hxS hm
      exact hleft.trans hright
    · apply ih a b hab
      intro x hx hxS
      apply hd x hx
      intro hm
      rcases Finset.mem_insert.mp hm with he | hm
      · subst x
        exact hin hx
      · exact hxS hm

/-- 有限個の接続点では連続性だけを使い、全域での一定性を導く。 -/
theorem real_constant_off_finset (S : Finset ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hd : ∀ x, x ∉ S → HasDerivAt f 0 x) (a b : ℝ) : f a = f b := by
  rcases le_total a b with hab | hba
  · exact real_constant_interval_off_finset S f hf a b hab (fun x _ hx => hd x hx)
  · exact (real_constant_interval_off_finset S f hf b a hba (fun x _ hx => hd x hx)).symm


/-! ## 9.1　任意の二つの解に対する局所保存式 -/

section FiniteForms
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- u†Jv。まず二つの独立な引数について保存を証明する。 -/
def form (J : Matrix ι ι ℂ) (u v : ι → ℂ) : ℂ := star u ⬝ᵥ (J.mulVec v)

theorem form_hasDerivAt (J : Matrix ι ι ℂ) (u v : ℝ → ι → ℂ)
    (u' v' : ι → ℂ) (x : ℝ) (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun t => form J (u t) (v t))
      (form J u' (v x) + form J (u x) v') x := by
  have hU (i : ι) : HasDerivAt (fun t => u t i) (u' i) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i).hasFDerivAt.comp_hasDerivAt x hu
  have hJv := (matrixGenerator J).hasFDerivAt.comp_hasDerivAt x hv
  have hV (i : ι) : HasDerivAt (fun t => (J.mulVec (v t)) i) (J.mulVec v' i) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i).hasFDerivAt.comp_hasDerivAt x hJv
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hU i).star.mul (hV i))
  simpa only [form, dotProduct, Pi.star_apply, Finset.sum_add_distrib] using hd

omit [DecidableEq ι] in
theorem form_derivative_identity (J B : Matrix ι ι ℂ) (u v : ι → ℂ) :
    form J (B.mulVec u) v + form J u (B.mulVec v) =
      form (B.conjTranspose * J + J * B) u v := by
  simp only [form, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_mulVec]

/-- 係数は評価点での値だけを使う。空間依存の自己共役係数にも適用できる。 -/
theorem form_hasDerivAt_zero (J B : Matrix ι ι ℂ)
    (hB : B.conjTranspose * J + J * B = 0) (u v : ℝ → ι → ℂ) (x : ℝ)
    (hu : HasDerivAt u (B.mulVec (u x)) x) (hv : HasDerivAt v (B.mulVec (v x)) x) :
    HasDerivAt (fun t => form J (u t) (v t)) 0 x := by
  have hd := form_hasDerivAt J u v _ _ x hu hv
  rw [form_derivative_identity, hB] at hd
  simpa only [form, Matrix.zero_mulVec, dotProduct_zero] using hd

theorem form_conserved (J B : Matrix ι ι ℂ)
    (hB : B.conjTranspose * J + J * B = 0) (u v : ℝ → ι → ℂ)
    (hu : ∀ x, HasDerivAt u (B.mulVec (u x)) x)
    (hv : ∀ x, HasDerivAt v (B.mulVec (v x)) x) (x y : ℝ) :
    form J (u x) (v x) = form J (u y) (v y) :=
  is_const_of_deriv_eq_zero
    (fun t => (form_hasDerivAt_zero J B hB u v t (hu t) (hv t)).differentiableAt)
    (fun t => (form_hasDerivAt_zero J B hB u v t (hu t) (hv t)).deriv) x y

omit [DecidableEq ι] in
theorem form_congruence (J T : Matrix ι ι ℂ) (u v : ι → ℂ) :
    form J (T.mulVec u) (T.mulVec v) = form (T.conjTranspose * J * T) u v := by
  simp only [form, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- 任意のu,vでの恒等式から行列の等式を取り出す。 -/
theorem matrix_eq_of_form_eq (A B : Matrix ι ι ℂ)
    (h : ∀ u v : ι → ℂ, form A u v = form B u v) : A = B := by
  ext i j
  have he := h (Pi.single i 1) (Pi.single j 1)
  simpa [form, ← Pi.single_star] using he

/-- 正定値性を要求しない保存形式。 -/
def PreservesForm (J T : Matrix ι ι ℂ) : Prop := T.conjTranspose * J * T = J

theorem transferMatrix_preserves_form (J B : Matrix ι ι ℂ)
    (hB : B.conjTranspose * J + J * B = 0) (x : ℝ) :
    PreservesForm J (transferMatrix B x) := by
  apply matrix_eq_of_form_eq
  intro u v
  rw [← form_congruence, transferMatrix_mulVec, transferMatrix_mulVec]
  have he := form_conserved J B hB (matrixFlow B u) (matrixFlow B v)
    (matrixFlow_hasDerivAt B u) (matrixFlow_hasDerivAt B v) x 0
  simpa only [matrixFlow_zero] using he

omit [DecidableEq ι] in
theorem preservesForm_mul (J A B : Matrix ι ι ℂ)
    (hA : PreservesForm J A) (hB : PreservesForm J B) : PreservesForm J (A * B) := by
  unfold PreservesForm at *
  calc
    (A * B).conjTranspose * J * (A * B) =
      B.conjTranspose * (A.conjTranspose * J * A) * B := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
    _ = J := by rw [hA, hB]

end FiniteForms

/-! ## 9.2　不定形式Jと伝達行列 -/

section FluxMatrix
variable {N : ℕ} [NeZero N]

/-- y=(f,f')に対するWronskian流束の行列。 -/
def fluxMatrix (N : ℕ) [NeZero N] : ScatteringMatrix N :=
  Matrix.fromBlocks 0 ((-Complex.I / 2) • (1 : InternalMatrix N))
    ((Complex.I / 2) • (1 : InternalMatrix N)) 0

theorem generator_preserves_flux {C : InternalMatrix N} (hC : C.IsHermitian) :
    (stationaryGenerator C).conjTranspose * fluxMatrix N +
      fluxMatrix N * stationaryGenerator C = 0 := by
  simp only [stationaryGenerator, fluxMatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero, Matrix.conjTranspose_one,
    hC.eq, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    zero_add, add_zero, Matrix.mul_smul, Matrix.smul_mul]
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.smul_apply] <;> ring

theorem stationaryTransfer_preserves_flux {C : InternalMatrix N} (hC : C.IsHermitian) (x : ℝ) :
    PreservesForm (fluxMatrix N) (transferMatrix (stationaryGenerator C) x) :=
  transferMatrix_preserves_form _ _ (generator_preserves_flux hC) x

theorem totalTransfer_preserves_flux (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) :
    PreservesForm (fluxMatrix N) (totalTransfer p s k layers) := by
  induction layers with
  | nil => simp [totalTransfer, PreservesForm]
  | cons l rest ih =>
    exact preservesForm_mul _ _ _ ih
      (stationaryTransfer_preserves_flux (layerCoefficient_hermitian p s k l) l.width)

/-- 実数としての流束。後でWronskianの表式との一致を証明する。 -/
def stateFlux (y : StateVector N) : ℝ := (form (fluxMatrix N) y y).re

theorem fluxMatrix_action (y : StateVector N) :
    (fluxMatrix N).mulVec y =
      packState ((-Complex.I / 2) • stateSlope y) ((Complex.I / 2) • stateValue y) := by
  rw [fluxMatrix, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    zero_add, add_zero, packState, Function.comp_def]
  rfl

omit [NeZero N] in
theorem star_packState (f g : InternalVector N) :
    star (packState f g) = packState (star f) (star g) := by
  funext i
  cases i <;> rfl

theorem complex_flux_identity (z : ℂ) :
    (-Complex.I / 2) * z + (Complex.I / 2) * star z = (z.im : ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem form_fluxMatrix_pack (f g : InternalVector N) :
    form (fluxMatrix N) (packState f g) (packState f g) = ((star f ⬝ᵥ g).im : ℂ) := by
  rw [form, fluxMatrix_action, packState_value, packState_slope, star_packState]
  change Sum.elim (star f) (star g) ⬝ᵥ
    Sum.elim ((-Complex.I / 2) • g) ((Complex.I / 2) • f) = _
  rw [sumElim_dotProduct_sumElim, dotProduct_smul, dotProduct_smul, Matrix.star_dotProduct g f]
  simpa only [smul_eq_mul] using complex_flux_identity (star f ⬝ᵥ g)

theorem stateFlux_pack (f g : InternalVector N) :
    stateFlux (packState f g) = (star f ⬝ᵥ g).im := by
  unfold stateFlux
  rw [form_fluxMatrix_pack]
  rfl

theorem stateFlux_eq_wronskian (y : StateVector N) :
    stateFlux y = (star (stateValue y) ⬝ᵥ stateSlope y).im := by
  simpa only [packState_parts] using stateFlux_pack (stateValue y) (stateSlope y)

theorem wronskian_complex_formula (f g : InternalVector N) :
    (stateFlux (packState f g) : ℂ) =
      (1 / (2 * Complex.I)) * (star f ⬝ᵥ g - star g ⬝ᵥ f) := by
  have hscalar : (1 : ℂ) / (2 * Complex.I) = -Complex.I / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]
  rw [stateFlux_pack, Matrix.star_dotProduct g f, hscalar]
  rw [← complex_flux_identity (star f ⬝ᵥ g)]
  ring

theorem fluxMatrix_hermitian : (fluxMatrix N).IsHermitian := by
  change (fluxMatrix N).conjTranspose = fluxMatrix N
  simp [fluxMatrix, Matrix.fromBlocks_conjTranspose]

/-- 正負の二次形式を持つ状態の実在。不定性を名前だけで済ませない。 -/
theorem fluxMatrix_indefinite :
    ∃ u v : StateVector N, stateFlux u = 1 ∧ stateFlux v = -1 := by
  refine ⟨packState (Pi.single (0 : Grid N) 1) (Pi.single (0 : Grid N) Complex.I),
    packState (Pi.single (0 : Grid N) 1) (Pi.single (0 : Grid N) (-Complex.I)), ?_, ?_⟩
  · rw [stateFlux_pack]
    simp [← Pi.single_star]
  · rw [stateFlux_pack]
    simp [← Pi.single_star]

theorem fluxMatrix_not_posSemidef : ¬(fluxMatrix N).PosSemidef := by
  obtain ⟨u, v, hu, hv⟩ := fluxMatrix_indefinite (N := N)
  intro hJ
  have h := hJ.re_dotProduct_nonneg v
  change 0 ≤ stateFlux v at h
  rw [hv] at h
  norm_num at h

theorem chain_flux_conserved (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (y0 yEnd : StateVector N) (h : IsLayerChain p s k layers y0 yEnd) :
    stateFlux yEnd = stateFlux y0 := by
  have he := (layerChain_iff p s k layers y0 yEnd).mp h
  rw [← totalTransfer_action p s k layers y0] at he
  rw [he]
  unfold stateFlux
  rw [form_congruence, totalTransfer_preserves_flux p s k layers]

end FluxMatrix

/-- 任意の複素数a,bについて、混合項の虚部が打ち消し合う恒等式。 -/
theorem scalar_flux_algebra (κ : ℝ) (a b : ℂ) :
    (star (a + b) * (phaseRate κ * (a - b))).im =
      κ * (Complex.normSq a - Complex.normSq b) := by
  simp [phaseRate, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem planeWave_normSq (a x : ℝ) : Complex.normSq (planeWave a x) = 1 := by
  rw [← Complex.sq_norm]
  simp [planeWave, phaseRate, Complex.norm_exp]

theorem twoWaves_flux (κ x : ℝ) (a b : ℂ) :
    (star (planeWave κ x * a + planeWave (-κ) x * b) *
      (phaseRate κ * planeWave κ x * a + phaseRate (-κ) * planeWave (-κ) x * b)).im =
      κ * (Complex.normSq a - Complex.normSq b) := by
  have hrate : phaseRate (-κ) = -phaseRate κ := by simp [phaseRate]
  have heq : phaseRate κ * planeWave κ x * a + phaseRate (-κ) * planeWave (-κ) x * b =
      phaseRate κ * (planeWave κ x * a - planeWave (-κ) x * b) := by
    rw [hrate]
    ring
  rw [heq, scalar_flux_algebra]
  simp only [map_mul, planeWave_normSq, one_mul]

/-! ## 9.3　任意の複素振幅と外部流束 -/

section ExteriorAmplitudes
variable {N : ℕ} [NeZero N]

def exteriorUnitary (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    InternalMatrix N := (exteriorDefect_hermitian p s k).eigenvectorUnitary

theorem exteriorUnitary_unitary (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) : IsUnitaryMatrix (exteriorUnitary p s k) :=
  ⟨unitary.coe_star_mul_self _, unitary.coe_mul_star_self _⟩

theorem unitary_pairing (U : InternalMatrix N) (hU : IsUnitaryMatrix U)
    (u v : InternalVector N) :
    star (U.mulVec u) ⬝ᵥ (U.mulVec v) = star u ⬝ᵥ v := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    hU.1, Matrix.vecMul_one]

def profileCoefficients (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (aPlus aMinus : InternalVector N) (x : ℝ) : InternalVector N := fun α =>
  planeWave (channelWaveNumber p s k α) x * aPlus α +
    planeWave (-channelWaveNumber p s k α) x * aMinus α

def slopeCoefficients (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (aPlus aMinus : InternalVector N) (x : ℝ) : InternalVector N := fun α =>
  phaseRate (channelWaveNumber p s k α) * planeWave (channelWaveNumber p s k α) x * aPlus α +
    phaseRate (-channelWaveNumber p s k α) * planeWave (-channelWaveNumber p s k α) x * aMinus α

theorem exteriorProfile_repr (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (aPlus aMinus : InternalVector N) (x : ℝ) :
    exteriorProfile p s k aPlus aMinus x =
      (exteriorUnitary p s k).mulVec (profileCoefficients p s k aPlus aMinus x) := by
  ext n
  change (∑ α : Grid N, profileCoefficients p s k aPlus aMinus x α *
    (exteriorBasis p s k α) n) =
    ∑ α : Grid N, (exteriorBasis p s k α) n * profileCoefficients p s k aPlus aMinus x α
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem exteriorSlope_repr (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (aPlus aMinus : InternalVector N) (x : ℝ) :
    exteriorSlope p s k aPlus aMinus x =
      (exteriorUnitary p s k).mulVec (slopeCoefficients p s k aPlus aMinus x) := by
  ext n
  change (∑ α : Grid N, slopeCoefficients p s k aPlus aMinus x α *
    (exteriorBasis p s k α) n) =
    ∑ α : Grid N, (exteriorBasis p s k α) n * slopeCoefficients p s k aPlus aMinus x α
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Σα kα |aα|²。通常の規格化前の、流束に現れる重み付き二乗和。 -/
def weightedNorm (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (a : InternalVector N) : ℝ :=
  ∑ α : Grid N, channelWaveNumber p s k α * Complex.normSq (a α)

def channelMomentumMatrix (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) : InternalMatrix N :=
  Matrix.diagonal (fun α => (channelWaveNumber p s k α : ℂ))

/-- 重み付き二乗和とa†Kaの複素数としての一致。二次形式が実数であることも示す。 -/
theorem weightedNorm_quadratic (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (a : InternalVector N) :
    form (channelMomentumMatrix p s k) a a = (weightedNorm p s k a : ℂ) := by
  simp only [form, channelMomentumMatrix, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
  rw [weightedNorm, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  change star (a α) * ((channelWaveNumber p s k α : ℂ) * a α) =
    (channelWaveNumber p s k α : ℂ) * (star (a α) * a α)
  ring

theorem weightedNorm_eq_re_quadratic (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (a : InternalVector N) :
    weightedNorm p s k a = (form (channelMomentumMatrix p s k) a a).re := by
  rw [weightedNorm_quadratic]
  rfl

theorem exterior_flux_identity (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (aPlus aMinus : InternalVector N) (x : ℝ) :
    (star (exteriorProfile p s k aPlus aMinus x) ⬝ᵥ
      exteriorSlope p s k aPlus aMinus x).im =
      weightedNorm p s k aPlus - weightedNorm p s k aMinus := by
  rw [exteriorProfile_repr, exteriorSlope_repr,
    unitary_pairing _ (exteriorUnitary_unitary p s k)]
  change Complex.imAddGroupHom
    (∑ α : Grid N, star (profileCoefficients p s k aPlus aMinus x α) *
      slopeCoefficients p s k aPlus aMinus x α) = _
  rw [map_sum]
  change (∑ α : Grid N,
    (star (profileCoefficients p s k aPlus aMinus x α) *
      slopeCoefficients p s k aPlus aMinus x α).im) = _
  simp only [profileCoefficients, slopeCoefficients,
    twoWaves_flux, mul_sub, Finset.sum_sub_distrib, weightedNorm]

end ExteriorAmplitudes

/-! ### 第八章の散乱解・端点条件への適用 -/

section GlobalConservation
variable {N : ℕ} [NeZero N]

theorem stateFlux_continuous : Continuous (stateFlux : StateVector N → ℝ) := by
  have hform : Continuous (fun y : StateVector N => form (fluxMatrix N) y y) := by
    change Continuous (fun y : StateVector N =>
      ∑ i : ScatteringChannel N, star (y i) * ((fluxMatrix N).mulVec y) i)
    apply continuous_finset_sum
    intro i _
    exact (continuous_apply i).star.mul
      ((continuous_apply i).comp (matrixGenerator (fluxMatrix N)).continuous)
  exact Complex.continuous_re.comp hform

theorem stateFlux_hasDerivAt_zero {C : InternalMatrix N} (hC : C.IsHermitian)
    (y : ℝ → StateVector N) (x : ℝ)
    (hy : HasDerivAt y ((stationaryGenerator C).mulVec (y x)) x) :
    HasDerivAt (fun t => stateFlux (y t)) 0 x := by
  have hd := form_hasDerivAt_zero (fluxMatrix N) (stationaryGenerator C)
    (generator_preserves_flux hC) y y x hy hy
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  simpa only [stateFlux, Function.comp_def, Complex.reCLM_apply, Complex.zero_re] using hreal

/-- 接続点を含む全実数上で、任意の散乱解の流束は一定である。 -/
theorem scattering_flux_conserved (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N)
    (y : ℝ → StateVector N) (h : IsScatteringSolution p s k layers a y) (x z : ℝ) :
    stateFlux (y x) = stateFlux (y z) := by
  apply real_constant_off_finset (interfaces layers).toFinset (fun t => stateFlux (y t))
    (stateFlux_continuous.comp h.1)
  intro t ht
  have htList : t ∉ interfaces layers := by
    simpa only [List.mem_toFinset] using ht
  have hC : (freeMassSquared p s + layeredPotential layers t -
      realScalarMatrix (reducedFrequencySquared k)).IsHermitian :=
    ((MassMatrix.freeMassSquared_hermitian p s).add
      (layeredPotential_hermitian layers t)).sub (MassMatrix.scalarMatrix_hermitian _)
  exact stateFlux_hasDerivAt_zero hC y t (h.2.1 t htList)

theorem leftExteriorState_flux (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (a : ExteriorAmplitudes N) (x : ℝ) :
    stateFlux (leftExteriorState p s k a x) =
      weightedNorm p s k (fun α => a.incoming (Sum.inl α)) -
        weightedNorm p s k (fun α => a.outgoing (Sum.inl α)) := by
  unfold leftExteriorState
  rw [stateFlux_pack, exterior_flux_identity]

theorem rightExteriorState_flux (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (width : ℝ) (a : ExteriorAmplitudes N) (x : ℝ) :
    stateFlux (rightExteriorState p s k width a x) =
      weightedNorm p s k (fun α => a.outgoing (Sum.inr α)) -
        weightedNorm p s k (fun α => a.incoming (Sum.inr α)) := by
  unfold rightExteriorState
  rw [stateFlux_pack, exterior_flux_identity]

theorem leftExteriorState_flux_quadratic (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (a : ExteriorAmplitudes N) (x : ℝ) :
    stateFlux (leftExteriorState p s k a x) =
      (form (channelMomentumMatrix p s k) (fun α => a.incoming (Sum.inl α))
        (fun α => a.incoming (Sum.inl α))).re -
      (form (channelMomentumMatrix p s k) (fun α => a.outgoing (Sum.inl α))
        (fun α => a.outgoing (Sum.inl α))).re := by
  rw [leftExteriorState_flux, weightedNorm_eq_re_quadratic, weightedNorm_eq_re_quadratic]

theorem rightExteriorState_flux_quadratic (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (width : ℝ) (a : ExteriorAmplitudes N) (x : ℝ) :
    stateFlux (rightExteriorState p s k width a x) =
      (form (channelMomentumMatrix p s k) (fun α => a.outgoing (Sum.inr α))
        (fun α => a.outgoing (Sum.inr α))).re -
      (form (channelMomentumMatrix p s k) (fun α => a.incoming (Sum.inr α))
        (fun α => a.incoming (Sum.inr α))).re := by
  rw [rightExteriorState_flux, weightedNorm_eq_re_quadratic, weightedNorm_eq_re_quadratic]

def incomingFlux (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (a : ExteriorAmplitudes N) : ℝ :=
  weightedNorm p s k (fun α => a.incoming (Sum.inl α)) +
    weightedNorm p s k (fun α => a.incoming (Sum.inr α))

def outgoingFlux (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (a : ExteriorAmplitudes N) : ℝ :=
  weightedNorm p s k (fun α => a.outgoing (Sum.inl α)) +
    weightedNorm p s k (fun α => a.outgoing (Sum.inr α))

theorem scattering_amplitudes_fluxBalance (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N)
    (y : ℝ → StateVector N) (h : IsScatteringSolution p s k layers a y) :
    incomingFlux p s k a = outgoingFlux p s k a := by
  have he := scattering_flux_conserved p s k layers a y h 0 (totalWidth layers)
  rw [h.2.2.1 0 le_rfl, h.2.2.2 (totalWidth layers) le_rfl,
    leftExteriorState_flux, rightExteriorState_flux] at he
  unfold incomingFlux outgoingFlux
  linarith

/-- 出射振幅を構成する前にも、端点条件を満たす振幅の流束保存は導ける。 -/
theorem boundaryMatching_fluxBalance (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N)
    (h : BoundaryMatching p s k layers a) : incomingFlux p s k a = outgoingFlux p s k a := by
  have he : stateFlux ((totalTransfer p s k layers).mulVec (leftExteriorState p s k a 0)) =
      stateFlux (leftExteriorState p s k a 0) := by
    unfold stateFlux
    rw [form_congruence, totalTransfer_preserves_flux p s k layers]
  rw [h, leftExteriorState_flux, rightExteriorState_flux] at he
  unfold incomingFlux outgoingFlux
  linarith

theorem weightedNorm_nonneg (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hOpen : AllExteriorChannelsOpen p s k) (a : InternalVector N) :
    0 ≤ weightedNorm p s k a :=
  Finset.sum_nonneg (fun α _ =>
    mul_nonneg (channelWaveNumber_pos p s k hOpen α).le (Complex.normSq_nonneg _))

theorem weightedNorm_eq_zero_iff (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hOpen : AllExteriorChannelsOpen p s k) (a : InternalVector N) :
    weightedNorm p s k a = 0 ↔ a = 0 := by
  constructor
  · intro hz
    have hnonneg (α : Grid N) : 0 ≤ channelWaveNumber p s k α * Complex.normSq (a α) :=
      mul_nonneg (channelWaveNumber_pos p s k hOpen α).le (Complex.normSq_nonneg _)
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun α _ => hnonneg α)).mp hz
    funext α
    have he := hterms α (Finset.mem_univ α)
    have hsq := (mul_eq_zero.mp he).resolve_left (channelWaveNumber_pos p s k hOpen α).ne'
    exact Complex.normSq_eq_zero.mp hsq
  · intro hz
    simp only [hz, weightedNorm, Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]

end GlobalConservation

/-!
## 証明範囲の確認

* form_hasDerivAt_zero：局所的な半双線形保存式。
* generator_preserves_flux：自己共役なCからB†J+JB=0。
* wronskian_complex_formula / stateFlux_eq_wronskian：jの表式とy†Jyの対応。
* fluxMatrix_hermitian / fluxMatrix_indefinite / fluxMatrix_not_posSemidef：Jの自己共役性と不定性。
* transferMatrix_preserves_form / totalTransfer_preserves_flux：T†JT=J。
* chain_flux_conserved：第八章の局所解の有限接続に対する保存。
* scattering_flux_conserved：第八章の任意の大域散乱解に対する、接続点を含む保存。
* scalar_flux_algebra / exterior_flux_identity：任意の複素振幅に対する流束恒等式。
* weightedNorm_quadratic / leftExteriorState_flux_quadratic / rightExteriorState_flux_quadratic：
  K=diag(kα)を使った行列表現との一致。
* scattering_amplitudes_fluxBalance / boundaryMatching_fluxBalance：入射総流束と出射総流束の一致。
* weightedNorm_nonneg / weightedNorm_eq_zero_iff：開チャネル条件の下での正値性。

全域保存の定理は、解が存在すれば成り立つという定理であり、
任意の入射条件に対応する解の存在を先取りしない。
有限チャネルの静的波動散乱に関する保存則であり、量子場理論のS行列や
独立した三時間発展の整合性を証明したものではない。
-/

#print axioms form_hasDerivAt_zero
#print axioms generator_preserves_flux
#print axioms wronskian_complex_formula
#print axioms fluxMatrix_indefinite
#print axioms transferMatrix_preserves_form
#print axioms totalTransfer_preserves_flux
#print axioms chain_flux_conserved
#print axioms real_constant_off_finset
#print axioms scattering_flux_conserved
#print axioms exterior_flux_identity
#print axioms weightedNorm_quadratic
#print axioms leftExteriorState_flux_quadratic
#print axioms rightExteriorState_flux_quadratic
#print axioms scattering_amplitudes_fluxBalance
#print axioms boundaryMatching_fluxBalance
#print axioms weightedNorm_eq_zero_iff

end WronskianFlux
end TwelveDimensionalPhaseSpace
