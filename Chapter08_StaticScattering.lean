import Chapter07_EnergyStability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.FinCases


set_option autoImplicit false

/-!
# 第八章　静的な有限チャネル散乱問題の定義

## 対象と到達点

自己共役な有限層障壁を、一つの外部空間方向xに沿って配置する。
外部の時間τと横方向の波数を固定した平面波

    Φ(τ,x,x⊥) = exp(-iωτ) exp(ik₁x₁) exp(ik₂x₂) f(x)
    Ω² = ω² - |k⊥|²

を第三章の方程式に代入し、各成分について

    f'' + [Ω²I - M₀² - V(x)]f = 0

へ帰着することを証明する。分離定理ではfの各成分が全体でC¹であるための
微分可能性と、評価点でf'が微分可能であることを要求する。
障壁の接続点ではf''を要求せず、状態 y=(f,f') の連続性を使う。

外部チャネルの基底、正の波数、左右の入射・出射振幅、接続条件を定義する。
各層の初期値解は指数作用素から構成し、それを複素行列に表す。
層内係数に正定値性を仮定せず、初期値解の存在・一意性を証明する。
全体の終状態は、右から通過順に作用する伝達行列の有限積で決まる。

本章の初期値問題と、任意の入射波を指定する散乱境界値問題は区別する。
後者の解の存在・一意性、散乱行列Sの構成、ユニタリティは後続章の課題である。
それらの結論をScatteringHypothesesやIsScatteringSolutionの仮定に含めない。

## 振幅と波数の規約

左外部：aL exp(+ikx) + bL exp(-ikx)。
右外部：bR exp(+ik(x-W)) + aR exp(-ik(x-W))。
aL,aRは入射、bL,bRは出射。Wは障壁全体の幅である。
正の周波数と exp(-iωτ) の規約の下で、正の空間位相を右向きに対応させる。
ここでの振幅は、まだ流束による規格化を行っていない。

外部では全チャネルが開いた場合を対象とし、k=0の閾値と閉チャネルを除く。
障壁内部の空間的な指数減衰・増大は許容し、観測時間の不安定性と混同しない。

## 利用方法と検証環境

第一〜第七章と同じmathlibプロジェクトで使用する。
先行章のコンパイル済みモジュールを配置した後：

    lake env lean -DwarningAsError=true Chapter08_StaticScattering.lean

Lean 4.24.0 / mathlib v4.24.0。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
末尾の #print axioms で主要定理の公理依存を確認する。
-/


noncomputable section
open scoped BigOperators ComplexOrder

namespace TwelveDimensionalPhaseSpace
namespace StaticScattering

/-! ## 8.1　定常平面波と方程式の分離 -/

def phaseRate (a : ℝ) : ℂ := (a : ℂ) * Complex.I
def planeWave (a x : ℝ) : ℂ := Complex.exp (phaseRate a * (x : ℂ))

theorem planeWave_hasDerivAt (a x : ℝ) :
    HasDerivAt (planeWave a) (phaseRate a * planeWave a x) x := by
  have h := (((hasDerivAt_id x).ofReal_comp).const_mul (phaseRate a)).cexp
  convert h using 1
  simp [planeWave, mul_comm]

theorem phaseRate_sq (a : ℝ) : phaseRate a ^ 2 = -((a ^ 2 : ℝ) : ℂ) := by
  simp only [phaseRate, mul_pow, Complex.I_sq, Complex.ofReal_pow]
  ring

theorem planeMul_second (a : ℝ) (c : ℂ) (x : ℝ) :
    deriv (deriv (fun r : ℝ => planeWave a r * c)) x =
      -((a ^ 2 : ℝ) : ℂ) * planeWave a x * c := by
  have hfirst : deriv (fun r : ℝ => planeWave a r * c) =
      fun r => phaseRate a * planeWave a r * c := by
    funext r
    exact ((planeWave_hasDerivAt a r).mul_const c).deriv
  rw [hfirst]
  rw [(((planeWave_hasDerivAt a x).const_mul (phaseRate a)).mul_const c).deriv]
  calc
    phaseRate a * (phaseRate a * planeWave a x) * c =
      phaseRate a ^ 2 * planeWave a x * c := by ring
    _ = _ := by rw [phaseRate_sq]

theorem constMul_second (c : ℂ) (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (x : ℝ) (hdf : DifferentiableAt ℝ (deriv f) x) :
    deriv (deriv (fun r : ℝ => c * f r)) x = c * deriv (deriv f) x := by
  have hfirst : deriv (fun r : ℝ => c * f r) = fun r => c * deriv f r := by
    funext r
    exact ((hf r).hasDerivAt.const_mul c).deriv
  rw [hfirst]
  exact (hdf.hasDerivAt.const_mul c).deriv

def planeFactor (k : ScatteringParameters) (τ : ObservedTime) (x : SpatialPosition) : ℂ :=
  planeWave (-k.frequency) τ * planeWave (k.transverseMomentum 0) (x 1) *
    planeWave (k.transverseMomentum 1) (x 2)

/-- 時間・横方向を平面波に分離した、元の4次元成分場。 -/
def separatedField {N : ℕ} (k : ScatteringParameters) (f : ℝ → InternalVector N) :
    CoordinateField N := fun τ x => planeFactor k τ x • f (x 0)

theorem planeFactor_ne_zero (k : ScatteringParameters) (τ : ObservedTime)
    (x : SpatialPosition) : planeFactor k τ x ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
    (Complex.exp_ne_zero _)

theorem separated_timeSecond {N : ℕ} (k : ScatteringParameters)
    (f : ℝ → InternalVector N) (τ : ObservedTime) (x : SpatialPosition) (i : Grid N) :
    deriv (deriv (fun t : ℝ => separatedField k f t x i)) τ =
      -((k.frequency ^ 2 : ℝ) : ℂ) * planeFactor k τ x * f (x 0) i := by
  have ht : (fun t : ℝ => separatedField k f t x i) = fun t =>
      planeWave (-k.frequency) t *
        (planeWave (k.transverseMomentum 0) (x 1) *
          planeWave (k.transverseMomentum 1) (x 2) * f (x 0) i) := by
    funext t
    simp only [separatedField, planeFactor, Pi.smul_apply, smul_eq_mul]
    ring
  rw [ht, planeMul_second]
  simp only [neg_sq, planeFactor]
  ring

theorem separated_spaceSecond_zero {N : ℕ} (k : ScatteringParameters)
    (f : ℝ → InternalVector N) (hf : ∀ i, Differentiable ℝ (fun r => f r i))
    (τ : ObservedTime) (x : SpatialPosition) (i : Grid N)
    (hdf : DifferentiableAt ℝ (deriv (fun r => f r i)) (x 0)) :
    deriv (deriv (fun r : ℝ => separatedField k f τ (Function.update x 0 r) i)) (x 0) =
      planeFactor k τ x * deriv (deriv (fun r => f r i)) (x 0) := by
  have hs : (fun r : ℝ => separatedField k f τ (Function.update x 0 r) i) =
      fun r => planeFactor k τ x * f r i := by
    funext r
    simp [separatedField, planeFactor]
  rw [hs]
  exact constMul_second _ _ (hf i) (x 0) hdf

theorem separated_spaceSecond_one {N : ℕ} (k : ScatteringParameters)
    (f : ℝ → InternalVector N) (τ : ObservedTime) (x : SpatialPosition) (i : Grid N) :
    deriv (deriv (fun r : ℝ => separatedField k f τ (Function.update x 1 r) i)) (x 1) =
      -((k.transverseMomentum 0 ^ 2 : ℝ) : ℂ) * planeFactor k τ x * f (x 0) i := by
  have hs : (fun r : ℝ => separatedField k f τ (Function.update x 1 r) i) = fun r =>
      planeWave (k.transverseMomentum 0) r *
        (planeWave (-k.frequency) τ * planeWave (k.transverseMomentum 1) (x 2) * f (x 0) i) := by
    funext r
    simp [separatedField, planeFactor]
    ring
  rw [hs, planeMul_second]
  unfold planeFactor
  ring

theorem separated_spaceSecond_two {N : ℕ} (k : ScatteringParameters)
    (f : ℝ → InternalVector N) (τ : ObservedTime) (x : SpatialPosition) (i : Grid N) :
    deriv (deriv (fun r : ℝ => separatedField k f τ (Function.update x 2 r) i)) (x 2) =
      -((k.transverseMomentum 1 ^ 2 : ℝ) : ℂ) * planeFactor k τ x * f (x 0) i := by
  have hs : (fun r : ℝ => separatedField k f τ (Function.update x 2 r) i) = fun r =>
      planeWave (k.transverseMomentum 1) r *
        (planeWave (-k.frequency) τ * planeWave (k.transverseMomentum 0) (x 1) * f (x 0) i) := by
    funext r
    simp [separatedField, planeFactor]
    ring
  rw [hs, planeMul_second]
  unfold planeFactor
  ring

section Reduction
variable {N : ℕ} [NeZero N]

def stationaryCoefficient (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (W : ℝ → InternalMatrix N) (x : ℝ) : InternalMatrix N :=
  realScalarMatrix (reducedFrequencySquared k) - freeMassSquared p s - W x

def stationaryResidual (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (W : ℝ → InternalMatrix N) (f : ℝ → InternalVector N)
    (x : ℝ) (i : Grid N) : ℂ :=
  deriv (deriv (fun r => f r i)) x + (stationaryCoefficient p s k W x).mulVec (f x) i

def longitudinalPotential (W : ℝ → InternalMatrix N) : Potential N := fun _ x => W (x 0)

/-- 静的な一方向ポテンシャルを、第三章の場のデータへ接続する。 -/
def scatteringModel (p : ModelParameters) (s : InternalShifts N) (W : ℝ → InternalMatrix N) :
    Discretization.FiniteModelData N := ⟨p, s, longitudinalPotential W⟩

theorem separated_residual (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (W : ℝ → InternalMatrix N) (f : ℝ → InternalVector N)
    (hf : ∀ i, Differentiable ℝ (fun r => f r i))
    (τ : ObservedTime) (x : SpatialPosition) (i : Grid N)
    (hdf : DifferentiableAt ℝ (deriv (fun r => f r i)) (x 0)) :
    Discretization.adoptedFieldResidual (scatteringModel p s W) (separatedField k f) τ x i =
      -(planeFactor k τ x * stationaryResidual p s k W f (x 0) i) := by
  unfold Discretization.adoptedFieldResidual
  rw [separated_timeSecond]
  rw [Fin.sum_univ_three]
  rw [separated_spaceSecond_zero k f hf τ x i hdf,
    separated_spaceSecond_one, separated_spaceSecond_two]
  change _ + (freeMassSquared p s + W (x 0)).mulVec
    (planeFactor k τ x • f (x 0)) i = _
  rw [Matrix.mulVec_smul]
  simp only [stationaryResidual, stationaryCoefficient, Matrix.sub_mulVec,
    Matrix.add_mulVec, realScalarMatrix, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
  unfold reducedFrequencySquared
  push_cast
  ring

theorem stationary_equation_at_iff (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (W : ℝ → InternalMatrix N) (f : ℝ → InternalVector N)
    (hf : ∀ i, Differentiable ℝ (fun r => f r i))
    (τ : ObservedTime) (x : SpatialPosition) (i : Grid N)
    (hdf : DifferentiableAt ℝ (deriv (fun r => f r i)) (x 0)) :
    Discretization.adoptedFieldResidual (scatteringModel p s W) (separatedField k f) τ x i = 0 ↔
      stationaryResidual p s k W f (x 0) i = 0 := by
  rw [separated_residual p s k W f hf τ x i hdf, neg_eq_zero, mul_eq_zero]
  simp only [planeFactor_ne_zero, false_or]

end Reduction


/-! ### 補助：符号に制限を置かない定数係数初期値問題 -/

section LinearEvolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Banach空間上の有界作用素の指数による、全実数での初期値発展。 -/
def linearFlow (B : E →L[ℝ] E) (y0 : E) (x : ℝ) : E :=
  (NormedSpace.exp ℝ (x • B)) y0

theorem linearFlow_hasDerivAt (B : E →L[ℝ] E) (y0 : E) (x : ℝ) :
    HasDerivAt (linearFlow B y0) (B (linearFlow B y0 x)) x := by
  have hd := (hasDerivAt_exp_smul_const' B x).clm_apply (hasDerivAt_const x y0)
  simpa only [linearFlow, ContinuousLinearMap.mul_apply, map_zero, add_zero] using hd

omit [CompleteSpace E] in
theorem linearFlow_zero (B : E →L[ℝ] E) (y0 : E) : linearFlow B y0 0 = y0 := by
  simp [linearFlow]

theorem integratingFactor_hasDerivAt (B : E →L[ℝ] E) (y : ℝ → E)
    (hy : ∀ x, HasDerivAt y (B (y x)) x) (x : ℝ) :
    HasDerivAt (fun t => (NormedSpace.exp ℝ (t • (-B))) (y t)) 0 x := by
  have hd := (hasDerivAt_exp_smul_const (-B) x).clm_apply (hy x)
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
    map_neg, neg_add_cancel] using hd

theorem linearFlow_unique (B : E →L[ℝ] E) (y : ℝ → E)
    (hy : ∀ x, HasDerivAt y (B (y x)) x) (x : ℝ) : y x = linearFlow B (y 0) x := by
  have hc := is_const_of_deriv_eq_zero
    (fun t => (integratingFactor_hasDerivAt B y hy t).differentiableAt)
    (fun t => (integratingFactor_hasDerivAt B y hy t).deriv) x 0
  simp only [zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_apply] at hc
  have he := congrArg
    (fun z : E => (NormedSpace.exp ℝ (x • B) : E →L[ℝ] E) z) hc
  have hi : NormedSpace.exp ℝ (x • B) * NormedSpace.exp ℝ (x • (-B)) = 1 := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl (x • B)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  change (NormedSpace.exp ℝ (x • B) * NormedSpace.exp ℝ (x • (-B))) (y x) =
    linearFlow B (y 0) x at he
  rw [hi, ContinuousLinearMap.one_apply] at he
  exact he

end LinearEvolution

section MatrixEvolution
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixGenerator (B : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) :=
  (LinearMap.toContinuousLinearMap B.toLin').restrictScalars ℝ

theorem matrixGenerator_apply (B : Matrix ι ι ℂ) (y : ι → ℂ) :
    matrixGenerator B y = B.mulVec y := rfl

def matrixFlow (B : Matrix ι ι ℂ) (y0 : ι → ℂ) (x : ℝ) : ι → ℂ :=
  linearFlow (matrixGenerator B) y0 x

theorem matrixFlow_hasDerivAt (B : Matrix ι ι ℂ) (y0 : ι → ℂ) (x : ℝ) :
    HasDerivAt (matrixFlow B y0) (B.mulVec (matrixFlow B y0 x)) x :=
  linearFlow_hasDerivAt (matrixGenerator B) y0 x

theorem matrixFlow_zero (B : Matrix ι ι ℂ) (y0 : ι → ℂ) : matrixFlow B y0 0 = y0 :=
  linearFlow_zero (matrixGenerator B) y0

theorem matrixFlow_complex_smul (B : Matrix ι ι ℂ) (c : ℂ) (y0 : ι → ℂ) (x : ℝ) :
    matrixFlow B (c • y0) x = c • matrixFlow B y0 x := by
  have hd (t : ℝ) : HasDerivAt (fun r => c • matrixFlow B y0 r)
      (matrixGenerator B (c • matrixFlow B y0 t)) t := by
    simpa only [matrixGenerator_apply, Matrix.mulVec_smul] using
      (matrixFlow_hasDerivAt B y0 t).const_smul c
  have hu := linearFlow_unique (matrixGenerator B) (fun r => c • matrixFlow B y0 r) hd x
  simpa only [matrixFlow_zero] using hu.symm

/-- 実変数で構成した発展が複素線形でもあることを、解の一意性から保証する。 -/
def transferLinearMap (B : Matrix ι ι ℂ) (x : ℝ) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun y0 := matrixFlow B y0 x
  map_add' u v := (NormedSpace.exp ℝ (x • matrixGenerator B)).map_add u v
  map_smul' c u := matrixFlow_complex_smul B c u x

/-- 指数作用素を標準成分基底で表した複素伝達行列。 -/
def transferMatrix (B : Matrix ι ι ℂ) (x : ℝ) : Matrix ι ι ℂ :=
  LinearMap.toMatrix' (transferLinearMap B x)

theorem transferMatrix_mulVec (B : Matrix ι ι ℂ) (x : ℝ) (y0 : ι → ℂ) :
    (transferMatrix B x).mulVec y0 = matrixFlow B y0 x :=
  LinearMap.toMatrix'_mulVec (transferLinearMap B x) y0

theorem transferMatrix_hasDerivAt (B : Matrix ι ι ℂ) (y0 : ι → ℂ) (x : ℝ) :
    HasDerivAt (fun t => (transferMatrix B t).mulVec y0)
      (B.mulVec ((transferMatrix B x).mulVec y0)) x := by
  simpa only [transferMatrix_mulVec] using matrixFlow_hasDerivAt B y0 x

theorem transferMatrix_zero (B : Matrix ι ι ℂ) : transferMatrix B 0 = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro y0
  simp only [Matrix.toLin'_apply, transferMatrix_mulVec, matrixFlow_zero, Matrix.one_mulVec]

theorem transferMatrix_add (B : Matrix ι ι ℂ) (x y : ℝ) :
    transferMatrix B (x + y) = transferMatrix B x * transferMatrix B y := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, transferMatrix_mulVec]
  have hc : Commute (x • matrixGenerator B) (y • matrixGenerator B) := by
    apply ContinuousLinearMap.ext
    intro w
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
      smul_smul, mul_comm]
  have hs := NormedSpace.exp_add_of_commute (𝕂 := ℝ) hc
  have hAdd := add_smul x y (matrixGenerator B)
  have hExp := (congrArg
    (fun T : (ι → ℂ) →L[ℝ] (ι → ℂ) => NormedSpace.exp ℝ T) hAdd).trans hs
  exact congrArg (fun T : (ι → ℂ) →L[ℝ] (ι → ℂ) => T v) hExp

theorem transferMatrix_inverse (B : Matrix ι ι ℂ) (x : ℝ) :
    transferMatrix B (-x) * transferMatrix B x = 1 ∧
      transferMatrix B x * transferMatrix B (-x) = 1 := by
  constructor
  · rw [← transferMatrix_add, neg_add_cancel, transferMatrix_zero]
  · rw [← transferMatrix_add, add_neg_cancel, transferMatrix_zero]

theorem matrix_initialValue_exists_unique (B : Matrix ι ι ℂ) (y0 : ι → ℂ) :
    ∃! y : ℝ → ι → ℂ, y 0 = y0 ∧ ∀ x, HasDerivAt y (B.mulVec (y x)) x := by
  refine ⟨matrixFlow B y0, ⟨matrixFlow_zero B y0, matrixFlow_hasDerivAt B y0⟩, ?_⟩
  intro y hy
  funext x
  have he := linearFlow_unique (matrixGenerator B) y hy.2 x
  simpa only [hy.1] using he

end MatrixEvolution

/-! ### 有限層障壁と、第一章の散乱仮定の実現 -/

section LayeredData
variable {N : ℕ} [NeZero N]

def totalWidth : List (BarrierLayer N) → ℝ
  | [] => 0
  | l :: rest => l.width + totalWidth rest

theorem totalWidth_nonneg (layers : List (BarrierLayer N)) : 0 ≤ totalWidth layers := by
  induction layers with
  | nil => exact le_rfl
  | cons l rest ih => exact add_nonneg l.width_pos.le ih

theorem layeredPotential_hermitian (layers : List (BarrierLayer N)) (x : ℝ) :
    (layeredPotential layers x).IsHermitian := by
  induction layers generalizing x with
  | nil => exact Matrix.isHermitian_zero
  | cons l rest ih =>
    simp only [layeredPotential]
    split_ifs
    · exact Matrix.isHermitian_zero
    · exact l.hermitian
    · exact ih _

theorem layeredPotential_left_zero (layers : List (BarrierLayer N)) (x : ℝ) (hx : x < 0) :
    layeredPotential layers x = 0 := by
  cases layers with
  | nil => rfl
  | cons l rest => simp only [layeredPotential, if_pos hx]

theorem layeredPotential_right_zero (layers : List (BarrierLayer N)) (x : ℝ)
    (hx : totalWidth layers ≤ x) : layeredPotential layers x = 0 := by
  induction layers generalizing x with
  | nil => rfl
  | cons l rest ih =>
    have hr := totalWidth_nonneg rest
    have hw := l.width_pos
    change l.width + totalWidth rest ≤ x at hx
    have h0 : ¬x < 0 := by linarith
    have hl : ¬x < l.width := by linarith
    simp only [layeredPotential, if_neg h0, if_neg hl]
    exact ih (x - l.width) (by linarith)

/-- 第一外部空間方向だけに依存し、全体として時間に依存しない障壁。 -/
def potentialFromLayers (layers : List (BarrierLayer N)) : Potential N :=
  fun _ x => layeredPotential layers (x 0)

theorem potentialFromLayers_representation (layers : List (BarrierLayer N)) :
    HasLayeredRepresentation (potentialFromLayers layers) := ⟨layers, fun _ _ => rfl⟩

theorem potentialFromLayers_static (layers : List (BarrierLayer N)) :
    IsStaticPotential (potentialFromLayers layers) :=
  static_of_layeredRepresentation (potentialFromLayers_representation layers)

theorem potentialFromLayers_hermitian (layers : List (BarrierLayer N)) :
    IsHermitianPotential (potentialFromLayers layers) :=
  fun _ x => layeredPotential_hermitian layers (x 0)

def layeredScatteringHypotheses (p : ModelParameters) (s : InternalShifts N)
    (layers : List (BarrierLayer N)) (k : ScatteringParameters)
    (hOpen : AllExteriorChannelsOpen p s k) :
    ScatteringHypotheses p s (potentialFromLayers layers) k :=
  ⟨potentialFromLayers_hermitian layers, potentialFromLayers_representation layers, hOpen⟩

end LayeredData

/-! ## 8.2　外部チャネルと正の波数 -/

section ExteriorChannels
variable {N : ℕ} [NeZero N]

def exteriorDefect (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    InternalMatrix N :=
  realScalarMatrix (reducedFrequencySquared k) - freeMassSquared p s

theorem exteriorDefect_hermitian (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) : (exteriorDefect p s k).IsHermitian :=
  (MassMatrix.scalarMatrix_hermitian _).sub (MassMatrix.freeMassSquared_hermitian p s)

/--
Ω²I-M₀²の正規直交固有基底を選ぶ。この基底はM₀²も対角化することを後で証明する。
固定した周波数での基底の選択であり、周波数を変えたときの一意なラベル付けは要求しない。
-/
def exteriorBasis (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :=
  (exteriorDefect_hermitian p s k).eigenvectorBasis

def channelDefect (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (α : Grid N) : ℝ :=
  (exteriorDefect_hermitian p s k).eigenvalues α

/-- M₀²の固有値。二乗質量という名前だけで非負性を仮定しない。 -/
def channelMassSquared (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (α : Grid N) : ℝ :=
  reducedFrequencySquared k - channelDefect p s k α

def channelWaveNumber (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (α : Grid N) : ℝ :=
  Real.sqrt (channelDefect p s k α)

theorem allExteriorChannelsOpen_iff (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) :
    AllExteriorChannelsOpen p s k ↔ ∀ α, 0 < channelDefect p s k α :=
  (exteriorDefect_hermitian p s k).posDef_iff_eigenvalues_pos

theorem allExteriorChannelsOpen_iff_waveNumbers (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) :
    AllExteriorChannelsOpen p s k ↔ ∀ α, 0 < channelWaveNumber p s k α := by
  simp only [allExteriorChannelsOpen_iff, channelWaveNumber, Real.sqrt_pos]

theorem channelWaveNumber_pos (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hOpen : AllExteriorChannelsOpen p s k) (α : Grid N) :
    0 < channelWaveNumber p s k α :=
  Real.sqrt_pos.mpr ((allExteriorChannelsOpen_iff p s k).mp hOpen α)

theorem channelWaveNumber_sq (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hOpen : AllExteriorChannelsOpen p s k) (α : Grid N) :
    channelWaveNumber p s k α ^ 2 =
      reducedFrequencySquared k - channelMassSquared p s k α := by
  have hd := (allExteriorChannelsOpen_iff p s k).mp hOpen α
  rw [channelWaveNumber, Real.sq_sqrt hd.le, channelMassSquared]
  ring

theorem exteriorBasis_massEigenvector (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (α : Grid N) :
    (freeMassSquared p s).mulVec ⇑(exteriorBasis p s k α) =
      channelMassSquared p s k α • ⇑(exteriorBasis p s k α) := by
  have he := (exteriorDefect_hermitian p s k).mulVec_eigenvectorBasis α
  change (exteriorDefect p s k).mulVec ⇑(exteriorBasis p s k α) =
    channelDefect p s k α • ⇑(exteriorBasis p s k α) at he
  rw [exteriorDefect, Matrix.sub_mulVec, realScalarMatrix, Matrix.smul_mulVec,
    Matrix.one_mulVec] at he
  have hsmul (r : ℝ) (v : InternalVector N) : (r : ℂ) • v = r • v := by
    ext n
    simp [Complex.real_smul]
  rw [hsmul] at he
  rw [channelMassSquared, sub_smul]
  rw [← he]
  abel

end ExteriorChannels

/-! ## 8.3　状態・接続条件・有限層の伝達 -/

section LayerTransfers
variable {N : ℕ}

abbrev StateVector (N : ℕ) := ScatteringChannel N → ℂ

def packState (f g : InternalVector N) : StateVector N := Sum.elim f g
def stateValue (y : StateVector N) : InternalVector N := fun n => y (Sum.inl n)
def stateSlope (y : StateVector N) : InternalVector N := fun n => y (Sum.inr n)

theorem packState_value (f g : InternalVector N) : stateValue (packState f g) = f := rfl
theorem packState_slope (f g : InternalVector N) : stateSlope (packState f g) = g := rfl

theorem packState_parts (y : StateVector N) : packState (stateValue y) (stateSlope y) = y := by
  funext i
  cases i <;> rfl

variable [NeZero N]

/-- y'=By、B=[[0,I],[C,0]]。C=M₀²+V-Ω²I。 -/
def stationaryGenerator (C : InternalMatrix N) : ScatteringMatrix N :=
  Matrix.fromBlocks 0 1 C 0

theorem stationaryGenerator_action (C : InternalMatrix N) (y : StateVector N) :
    (stationaryGenerator C).mulVec y = packState (stateSlope y) (C.mulVec (stateValue y)) := by
  rw [stationaryGenerator, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero,
    packState, Function.comp_def]
  rfl

def layerCoefficient (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (l : BarrierLayer N) : InternalMatrix N :=
  freeMassSquared p s + l.value - realScalarMatrix (reducedFrequencySquared k)

theorem layerCoefficient_hermitian (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (l : BarrierLayer N) :
    (layerCoefficient p s k l).IsHermitian :=
  ((MassMatrix.freeMassSquared_hermitian p s).add l.hermitian).sub
    (MassMatrix.scalarMatrix_hermitian _)

def layerTransfer (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (l : BarrierLayer N) : ScatteringMatrix N :=
  transferMatrix (stationaryGenerator (layerCoefficient p s k l)) l.width

/-- 最初の層が右端に来る積。T_all=T_last ... T_first。 -/
def totalTransfer (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    List (BarrierLayer N) → ScatteringMatrix N
  | [] => 1
  | l :: rest => totalTransfer p s k rest * layerTransfer p s k l

def propagateLayers (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    List (BarrierLayer N) → StateVector N → StateVector N
  | [], y0 => y0
  | l :: rest, y0 =>
      propagateLayers p s k rest
        (matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0 l.width)

theorem totalTransfer_action (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (y0 : StateVector N) :
    (totalTransfer p s k layers).mulVec y0 = propagateLayers p s k layers y0 := by
  induction layers generalizing y0 with
  | nil => exact Matrix.one_mulVec y0
  | cons l rest ih =>
    rw [totalTransfer, ← Matrix.mulVec_mulVec, layerTransfer, transferMatrix_mulVec, ih]
    rfl

/--
各層の初期値解を、前層の終状態を次層の初期値として接続する。
各解は全実数での解析的な延長を持ち、物理的には0≤x≤widthを使う。
この定義に終状態の値や保存則を先取りしない。
-/
def IsLayerChain (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    List (BarrierLayer N) → StateVector N → StateVector N → Prop
  | [], y0, yEnd => yEnd = y0
  | l :: rest, y0, yEnd =>
      ∃ y : ℝ → StateVector N,
        y 0 = y0 ∧
          (∀ x, HasDerivAt y
            ((stationaryGenerator (layerCoefficient p s k l)).mulVec (y x)) x) ∧
          IsLayerChain p s k rest (y l.width) yEnd

theorem layerChain_iff (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (y0 yEnd : StateVector N) :
    IsLayerChain p s k layers y0 yEnd ↔ yEnd = propagateLayers p s k layers y0 := by
  induction layers generalizing y0 yEnd with
  | nil => rfl
  | cons l rest ih =>
    constructor
    · rintro ⟨y, hy0, hy, hrest⟩
      have he : y l.width = matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0 l.width := by
        have hu := linearFlow_unique
          (matrixGenerator (stationaryGenerator (layerCoefficient p s k l))) y hy l.width
        simpa only [hy0] using hu
      have hEnd := (ih (y l.width) yEnd).mp hrest
      rw [he] at hEnd
      exact hEnd
    · intro hEnd
      refine ⟨matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0,
        matrixFlow_zero _ _, matrixFlow_hasDerivAt _ _, ?_⟩
      exact (ih _ _).mpr hEnd

theorem layered_initialValue_exists_unique (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (y0 : StateVector N) :
    ∃! yEnd : StateVector N, IsLayerChain p s k layers y0 yEnd := by
  refine ⟨(totalTransfer p s k layers).mulVec y0, ?_, ?_⟩
  · exact (layerChain_iff p s k layers y0 _).mpr (totalTransfer_action p s k layers y0)
  · intro yEnd hy
    exact ((layerChain_iff p s k layers y0 yEnd).mp hy).trans
      (totalTransfer_action p s k layers y0).symm

/-- 隣接する局所座標の間で、fとf'の双方を一致させる。 -/
def MatchesAt (yLeft yRight : ℝ → StateVector N) (width : ℝ) : Prop :=
  stateValue (yLeft width) = stateValue (yRight 0) ∧
    stateSlope (yLeft width) = stateSlope (yRight 0)

theorem adjacentLayers_match (C D : InternalMatrix N) (y0 : StateVector N) (width : ℝ) :
    MatchesAt (matrixFlow (stationaryGenerator C) y0)
      (matrixFlow (stationaryGenerator D)
        (matrixFlow (stationaryGenerator C) y0 width)) width := by
  simp only [MatchesAt, matrixFlow_zero, and_self]

theorem layer_initialValue_exists_unique (C : InternalMatrix N) (y0 : StateVector N) :
    ∃! y : ℝ → StateVector N, y 0 = y0 ∧
      ∀ x, HasDerivAt y
        (packState (stateSlope (y x)) (C.mulVec (stateValue (y x)))) x := by
  simpa only [stationaryGenerator_action] using
    matrix_initialValue_exists_unique (stationaryGenerator C) y0

theorem firstOrder_secondOrder (C : InternalMatrix N) (y : ℝ → StateVector N)
    (h : ∀ x, HasDerivAt y ((stationaryGenerator C).mulVec (y x)) x)
    (x : ℝ) (n : Grid N) :
    deriv (deriv (fun r => stateValue (y r) n)) x =
      (C.mulVec (stateValue (y x))) n := by
  have hf (t : ℝ) : HasDerivAt (fun r => stateValue (y r) n) (stateSlope (y t) n) t := by
    have H := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ScatteringChannel N => ℂ)
      (Sum.inl n)).hasFDerivAt.comp_hasDerivAt t (h t)
    change HasDerivAt (fun r => y r (Sum.inl n))
      (((stationaryGenerator C).mulVec (y t)) (Sum.inl n)) t at H
    rw [stationaryGenerator_action] at H
    exact H
  have hg := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ScatteringChannel N => ℂ)
    (Sum.inr n)).hasFDerivAt.comp_hasDerivAt x (h x)
  change HasDerivAt (fun r => y r (Sum.inr n))
    (((stationaryGenerator C).mulVec (y x)) (Sum.inr n)) x at hg
  rw [stationaryGenerator_action] at hg
  have hfun : deriv (fun r => stateValue (y r) n) = fun r => stateSlope (y r) n :=
    funext (fun t => (hf t).deriv)
  rw [hfun]
  exact hg.deriv

theorem layer_solution_stationaryResidual (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (l : BarrierLayer N) (y0 : StateVector N)
    (x : ℝ) (n : Grid N) :
    stationaryResidual p s k (fun _ => l.value)
      (fun r => stateValue (matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0 r)) x n = 0 := by
  have hC : stationaryCoefficient p s k (fun _ => l.value) x = -layerCoefficient p s k l := by
    unfold stationaryCoefficient layerCoefficient
    abel
  unfold stationaryResidual
  rw [firstOrder_secondOrder _ _ (matrixFlow_hasDerivAt _ _), hC, Matrix.neg_mulVec]
  exact add_neg_cancel _

end LayerTransfers

/-! ### 左右の振幅と散乱境界値問題の定義 -/

section AsymptoticData
variable {N : ℕ} [NeZero N]

structure ExteriorAmplitudes (N : ℕ) where
  incoming : ScatteringChannel N → ℂ
  outgoing : ScatteringChannel N → ℂ

def exteriorProfile (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (aPlus aMinus : InternalVector N) (x : ℝ) : InternalVector N :=
  fun n => ∑ α : Grid N,
    (planeWave (channelWaveNumber p s k α) x * aPlus α +
      planeWave (-channelWaveNumber p s k α) x * aMinus α) *
      (exteriorBasis p s k α) n

def exteriorSlope (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (aPlus aMinus : InternalVector N) (x : ℝ) : InternalVector N :=
  fun n => ∑ α : Grid N,
    (phaseRate (channelWaveNumber p s k α) * planeWave (channelWaveNumber p s k α) x * aPlus α +
      phaseRate (-channelWaveNumber p s k α) * planeWave (-channelWaveNumber p s k α) x * aMinus α) *
      (exteriorBasis p s k α) n

theorem exteriorProfile_hasDerivAt (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (aPlus aMinus : InternalVector N) (x : ℝ) (n : Grid N) :
    HasDerivAt (fun r => exteriorProfile p s k aPlus aMinus r n)
      (exteriorSlope p s k aPlus aMinus x n) x := by
  exact HasDerivAt.fun_sum (fun α _ =>
    (((planeWave_hasDerivAt (channelWaveNumber p s k α) x).mul_const (aPlus α)).add
      ((planeWave_hasDerivAt (-channelWaveNumber p s k α) x).mul_const (aMinus α))).mul_const
        ((exteriorBasis p s k α) n))

def leftExteriorState (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (a : ExteriorAmplitudes N) (x : ℝ) : StateVector N :=
  packState
    (exteriorProfile p s k (fun α => a.incoming (Sum.inl α))
      (fun α => a.outgoing (Sum.inl α)) x)
    (exteriorSlope p s k (fun α => a.incoming (Sum.inl α))
      (fun α => a.outgoing (Sum.inl α)) x)

def rightExteriorState (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (width : ℝ) (a : ExteriorAmplitudes N) (x : ℝ) : StateVector N :=
  packState
    (exteriorProfile p s k (fun α => a.outgoing (Sum.inr α))
      (fun α => a.incoming (Sum.inr α)) (x - width))
    (exteriorSlope p s k (fun α => a.outgoing (Sum.inr α))
      (fun α => a.incoming (Sum.inr α)) (x - width))

/-- 0と全幅Wを含む、全接続点の有限リスト。 -/
def interfaces : List (BarrierLayer N) → List ℝ
  | [] => [0]
  | l :: rest => 0 :: (interfaces rest).map (fun x => l.width + x)

/-- 入射・出射振幅について後続章で解く、有限次元の端点条件。 -/
def BoundaryMatching (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N) : Prop :=
  (totalTransfer p s k layers).mulVec (leftExteriorState p s k a 0) =
    rightExteriorState p s k (totalWidth layers) a (totalWidth layers)

/--
状態の連続性により、fとf'の接続を課す。ODEは接続点以外で要求する。
左右外部では、指定した入射・出射振幅の状態と一致させる。
この性質を満たすyや出射振幅の存在を、ここで仮定・証明してはいない。
-/
def IsScatteringSolution (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N) (y : ℝ → StateVector N) : Prop :=
  Continuous y ∧
    (∀ x, x ∉ interfaces layers → HasDerivAt y
      ((stationaryGenerator
        (freeMassSquared p s + layeredPotential layers x -
          realScalarMatrix (reducedFrequencySquared k))).mulVec (y x)) x) ∧
    (∀ x, x ≤ 0 → y x = leftExteriorState p s k a x) ∧
    (∀ x, totalWidth layers ≤ x → y x = rightExteriorState p s k (totalWidth layers) a x)

end AsymptoticData


/-!
## 証明範囲

* separated_residual / stationary_equation_at_iff：場の方程式から定常方程式への帰着。
* layeredPotential_hermitian / layeredPotential_left_zero / layeredPotential_right_zero：
  自己共役な有限区間障壁の具体的な実現。
* exteriorBasis_massEigenvector：外部の共通基底がM₀²の固有基底でもあること。
* allExteriorChannelsOpen_iff_waveNumbers / channelWaveNumber_sq：
  第一章の開チャネル条件と、kα>0、kα²=Ω²-mα²の対応。
* transferMatrix_hasDerivAt / matrix_initialValue_exists_unique：
  指数から構成した伝達が初期値方程式を解き、その解が一意であること。
* transferMatrix_add / transferMatrix_inverse：区間長の加法則と逆向きの伝達。
* firstOrder_secondOrder / layer_solution_stationaryResidual：
  一階化した初期値発展と、実際の定常二階方程式との接続。
* totalTransfer_action / layerChain_iff / layered_initialValue_exists_unique：
  有限層全体の終状態が逐次発展・行列積の双方で一致し、一意に定まること。
* adjacentLayers_match：隣接する局所解のfとf'が一致すること。
* exteriorProfile_hasDerivAt：定義した外部の傾きが、実際の成分微分に一致すること。

定義しただけで、まだ結論しないこと：

* IsScatteringSolutionを満たす大域的なyの構成。
* その大域的な解とBoundaryMatchingとの完全な必要十分性。
* 任意の入射振幅に対する散乱解・出射振幅の存在と一意性。
* Wronskian流束保存、流束規格化した散乱行列Sのユニタリティ。

初期値発展の存在は、両側から入射振幅を指定する境界値問題の可解性を
それだけで保証するものではない。後続章では保存形式と有限次元線形代数を使い、
この隔たりを埋める。伝達行列Tの逆行列を構成したことから、通常の正定値内積に
関するTのユニタリ性を結論することもしない。

第七章に残る、空間連続の時間発展の存在定理は、本章の定常有限チャネルODEの
初期値構成の前提にはしていない。
-/

#print axioms stationary_equation_at_iff
#print axioms layeredPotential_hermitian
#print axioms layeredPotential_right_zero
#print axioms exteriorBasis_massEigenvector
#print axioms allExteriorChannelsOpen_iff_waveNumbers
#print axioms channelWaveNumber_sq
#print axioms transferMatrix_hasDerivAt
#print axioms matrix_initialValue_exists_unique
#print axioms transferMatrix_inverse
#print axioms layer_solution_stationaryResidual
#print axioms layered_initialValue_exists_unique
#print axioms adjacentLayers_match
#print axioms exteriorProfile_hasDerivAt

end StaticScattering
end TwelveDimensionalPhaseSpace
