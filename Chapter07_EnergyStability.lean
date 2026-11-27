import Chapter06_FieldCorrespondence
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false

/-!
# 第七章　保存エネルギーと線形安定性

## この検証版の到達点

7.1 有限成分系について、初期値から全実時間にわたる解を構成し、
    一意性、エネルギー保存、変位・速度の一様な二乗評価を証明する。
    証明は有界な対称作用素を持つ実ヒルベルト空間に一般化している。
7.2 一定の質量行列M²に対し、各空間波数kの作用素 |k|²I+M² へ適用する。
    第五章の参照模型では、任意N≥1・任意kで下界 |k|²+1/9 を得る。
7.3 非有界作用素にも使えるよう、線形な定義域上の対称作用素と
    十分に正則な強解を明示し、条件付きの保存則・評価を証明する。
    -Δ+M²(x)の実際の定義域、自己共役性、解の存在はまだ構成していない。
7.4 正周波数発展 i∂τψ=√A ψ は、この二階方程式の証明と区別する。
    平方根、正周波数部分空間、ユニタリ群は本章では構成しない。

したがって、ロードマップ第七章全体の完了条件のうち、空間連続の場を
L²・有限エネルギー空間で扱う部分は未完了である。
各波数での評価だけを、フーリエ変換・積分の証明なしに場全体の評価とはしない。

## エネルギーと仮定

    u' = v,   v' = -Au
    E(u,v) = (‖v‖² + ⟪u,Au⟫_ℝ)/2

Aは時間に依存しない。対称性から E'=0 を導く。
A≥δIなら ‖v(t)‖²+δ‖u(t)‖²≤2E(0)。
δ>0なら変位と速度の双方に、時刻によらない上界が得られる。
エネルギー保存や正値性そのものを、解の定義に含めない。

複素内部空間には、複素内積の実部を取った実ヒルベルト構造を使う。
行列の自己共役性からこの対称性を導き、エネルギーの質量項を
Re(u†Au)と同一視する。通常の正のℓ²ノルムは第六章と共通である。

## 利用方法と検証環境

第一〜第六章と同じmathlibプロジェクトで使用する。
先行章のコンパイル済みモジュールを配置した後：

    lake env lean -DwarningAsError=true Chapter07_EnergyStability.lean

Lean 4.24.0 / mathlib v4.24.0。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
末尾の #print axioms で主要定理の公理依存を確認する。
-/

noncomputable section
open scoped BigOperators ComplexOrder
namespace TwelveDimensionalPhaseSpace
namespace EnergyStability

/-! ## 7.1　保存則・安定性・大域的な初期値解 -/

section RealHilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def energy (A : E →L[ℝ] E) (u v : E) : ℝ :=
  (‖v‖ ^ 2 + inner ℝ u (A u)) / 2

/-- 全実時間でu'=v、v'=-Auを満たす。HasDerivAtにより微分可能性も要求する。 -/
def IsOscillator (A : E →L[ℝ] E) (u v : ℝ → E) : Prop :=
  ∀ t, HasDerivAt u (v t) t ∧ HasDerivAt v (-(A (u t))) t

theorem oscillator_secondOrder (A : E →L[ℝ] E) (u v : ℝ → E)
    (h : IsOscillator A u v) (t : ℝ) : deriv (deriv u) t + A (u t) = 0 := by
  have hvel : deriv u = v := funext (fun s => (h s).1.deriv)
  rw [hvel, (h t).2.deriv, neg_add_cancel]

theorem energy_hasDerivAt_zero (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (u v : ℝ → E) (h : IsOscillator A u v) (t : ℝ) :
    HasDerivAt (fun s => energy A (u s) (v s)) 0 t := by
  have hu := (h t).1
  have hv := (h t).2
  have hAu := A.hasFDerivAt.comp_hasDerivAt t hu
  have hd := (hv.norm_sq.add (hu.inner ℝ hAu)).div_const 2
  have hz : (2 * inner ℝ (v t) (-(A (u t))) +
      (inner ℝ (u t) (A (v t)) + inner ℝ (v t) (A (u t)))) / 2 = 0 := by
    have hs : inner ℝ (A (u t)) (v t) = inner ℝ (u t) (A (v t)) := hA _ _
    rw [inner_neg_right, ← hs, real_inner_comm (A (u t)) (v t)]
    ring
  change HasDerivAt (fun s => energy A (u s) (v s))
    ((2 * inner ℝ (v t) (-(A (u t))) +
      (inner ℝ (u t) (A (v t)) + inner ℝ (v t) (A (u t)))) / 2) t at hd
  rw [hz] at hd
  exact hd

theorem energy_conserved (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (u v : ℝ → E) (h : IsOscillator A u v) (t s : ℝ) :
    energy A (u t) (v t) = energy A (u s) (v s) :=
  is_const_of_deriv_eq_zero
    (fun r => (energy_hasDerivAt_zero A hA u v h r).differentiableAt)
    (fun r => (energy_hasDerivAt_zero A hA u v h r).deriv) t s

/-- 二次形式による下界。δの正値性は、必要な定理で別途要求する。 -/
def HasOperatorLowerBound (A : E →L[ℝ] E) (δ : ℝ) : Prop :=
  ∀ u, δ * ‖u‖ ^ 2 ≤ inner ℝ u (A u)

theorem energy_coercive (A : E →L[ℝ] E) (δ : ℝ)
    (hA : HasOperatorLowerBound A δ) (u v : E) :
    ‖v‖ ^ 2 + δ * ‖u‖ ^ 2 ≤ 2 * energy A u v := by
  have h := hA u
  dsimp [energy]
  linarith

theorem stability_bound (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (δ : ℝ) (hLower : HasOperatorLowerBound A δ)
    (u v : ℝ → E) (h : IsOscillator A u v) (t : ℝ) :
    ‖v t‖ ^ 2 + δ * ‖u t‖ ^ 2 ≤ 2 * energy A (u 0) (v 0) := by
  rw [← energy_conserved A hA u v h t 0]
  exact energy_coercive A δ hLower _ _

theorem stability_bounds_separate (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (δ : ℝ) (hδ : 0 < δ) (hLower : HasOperatorLowerBound A δ)
    (u v : ℝ → E) (h : IsOscillator A u v) (t : ℝ) :
    ‖v t‖ ^ 2 ≤ 2 * energy A (u 0) (v 0) ∧
      ‖u t‖ ^ 2 ≤ 2 * energy A (u 0) (v 0) / δ := by
  have hb := stability_bound A hA δ hLower u v h t
  have huNon : 0 ≤ δ * ‖u t‖ ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
  have hvNon : 0 ≤ ‖v t‖ ^ 2 := sq_nonneg _
  constructor
  · linarith
  · apply (le_div_iff₀ hδ).mpr
    nlinarith

theorem zero_energy (A : E →L[ℝ] E) (δ : ℝ) (hδ : 0 < δ)
    (hLower : HasOperatorLowerBound A δ) (u v : E) (hE : energy A u v = 0) :
    u = 0 ∧ v = 0 := by
  have hb := energy_coercive A δ hLower u v
  rw [hE, mul_zero] at hb
  have huNon : 0 ≤ δ * ‖u‖ ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
  have hvNon : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have huZero : δ * ‖u‖ ^ 2 = 0 := le_antisymm (by linarith) huNon
  have huSq : ‖u‖ ^ 2 = 0 := (mul_eq_zero.mp huZero).resolve_left hδ.ne'
  have hvSq : ‖v‖ ^ 2 = 0 := le_antisymm (by linarith) hvNon
  exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp huSq), norm_eq_zero.mp (sq_eq_zero_iff.mp hvSq)⟩

theorem oscillator_sub (A : E →L[ℝ] E) (u v U V : ℝ → E)
    (h : IsOscillator A u v) (H : IsOscillator A U V) :
    IsOscillator A (u - U) (v - V) := by
  intro t
  constructor
  · exact (h t).1.sub (H t).1
  · have hd := (h t).2.sub (H t).2
    convert hd using 1
    simp only [Pi.sub_apply, map_sub]
    abel

theorem oscillator_unique (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (δ : ℝ) (hδ : 0 < δ) (hLower : HasOperatorLowerBound A δ)
    (u v U V : ℝ → E) (h : IsOscillator A u v) (H : IsOscillator A U V)
    (hu : u 0 = U 0) (hv : v 0 = V 0) : u = U ∧ v = V := by
  have hdiff := oscillator_sub A u v U V h H
  have hpoint (t : ℝ) : u t = U t ∧ v t = V t := by
    have he : energy A ((u - U) t) ((v - V) t) = 0 := by
      rw [energy_conserved A hA (u - U) (v - V) hdiff t 0]
      simp [Pi.sub_apply, hu, hv, energy]
    have hz := zero_energy A δ hδ hLower ((u - U) t) ((v - V) t) he
    exact ⟨sub_eq_zero.mp hz.1, sub_eq_zero.mp hz.2⟩
  exact ⟨funext (fun t => (hpoint t).1), funext (fun t => (hpoint t).2)⟩

theorem difference_stability_bound (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (δ : ℝ) (hLower : HasOperatorLowerBound A δ)
    (u v U V : ℝ → E) (h : IsOscillator A u v) (H : IsOscillator A U V) (t : ℝ) :
    ‖v t - V t‖ ^ 2 + δ * ‖u t - U t‖ ^ 2 ≤
      2 * energy A (u 0 - U 0) (v 0 - V 0) :=
  stability_bound A hA δ hLower (u - U) (v - V) (oscillator_sub A u v U V h H) t

variable [CompleteSpace E]

/-- 指数作用素に使う、位相空間上の有界作用素環の位相構造。 -/
local instance phaseOperator_topologicalRing :
    IsTopologicalRing ((E × E) →L[ℝ] (E × E)) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing ((E × E) →L[ℝ] (E × E)) inferInstance

/-- 一階化した生成子 B(u,v)=(v,-Au)。 -/
def generator (A : E →L[ℝ] E) : (E × E) →L[ℝ] E × E :=
  (ContinuousLinearMap.snd ℝ E E).prod
    (-(A.comp (ContinuousLinearMap.fst ℝ E E)))

/-- 任意初期値からの具体的な大域解 exp(tB)(u₀,v₀)。 -/
def flow (A : E →L[ℝ] E) (z : E × E) (t : ℝ) : E × E :=
  (NormedSpace.exp ℝ (t • generator A)) z

theorem flow_hasDerivAt (A : E →L[ℝ] E) (z : E × E) (t : ℝ) :
    HasDerivAt (flow A z) (generator A (flow A z t)) t := by
  have he := hasDerivAt_exp_smul_const' (generator A) t
  have hd := he.clm_apply (hasDerivAt_const t z)
  simpa only [flow, ContinuousLinearMap.mul_apply, map_zero,
    add_zero] using hd

omit [CompleteSpace E] in
theorem flow_zero (A : E →L[ℝ] E) (z : E × E) : flow A z 0 = z := by
  simp [flow]

theorem flow_isOscillator (A : E →L[ℝ] E) (z : E × E) :
    IsOscillator A (fun t => (flow A z t).1) (fun t => (flow A z t).2) := by
  intro t
  have hd := flow_hasDerivAt A z t
  constructor
  · simpa [generator, Function.comp_def] using
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t hd
  · simpa [generator, Function.comp_def] using
      (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t hd

theorem global_solution_exists_unique (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (δ : ℝ) (hδ : 0 < δ) (hLower : HasOperatorLowerBound A δ) (u0 v0 : E) :
    ∃! z : ℝ → E × E,
      z 0 = (u0, v0) ∧ IsOscillator A (fun t => (z t).1) (fun t => (z t).2) := by
  refine ⟨flow A (u0, v0), ⟨flow_zero A _, flow_isOscillator A _⟩, ?_⟩
  intro z hz
  have hu : (z 0).1 = (flow A (u0, v0) 0).1 := by rw [hz.1, flow_zero]
  have hv : (z 0).2 = (flow A (u0, v0) 0).2 := by rw [hz.1, flow_zero]
  have heq := oscillator_unique A hA δ hδ hLower _ _ _ _ hz.2
    (flow_isOscillator A (u0, v0)) hu hv
  funext t
  exact Prod.ext (congrFun heq.1 t) (congrFun heq.2 t)

end RealHilbert

/-! ## 7.2　複素質量行列と、自由場の各波数への適用 -/

section MatrixOscillators
variable {N : ℕ} [NeZero N]

/-- 複素内積の実部による実ヒルベルト構造。ノルムは同じ。 -/
local instance internalRealInner : InnerProductSpace ℝ (InternalHilbert N) :=
  InnerProductSpace.complexToReal

/-- 有限複素行列を、実変数の時間発展に使う有界実線形作用素へ移す。 -/
def matrixOperator (A : InternalMatrix N) : InternalHilbert N →L[ℝ] InternalHilbert N :=
  (LinearMap.toContinuousLinearMap A.toEuclideanLin).restrictScalars ℝ

theorem matrixOperator_symmetric {A : InternalMatrix N} (hA : A.IsHermitian) :
    (matrixOperator A).toLinearMap.IsSymmetric := by
  intro u v
  change RCLike.re (inner ℂ (A.toEuclideanLin u) v) =
    RCLike.re (inner ℂ u (A.toEuclideanLin v))
  exact congrArg RCLike.re ((Matrix.isHermitian_iff_isSymmetric.mp hA) u v)

theorem matrixOperator_quadratic (A : InternalMatrix N) (u : InternalHilbert N) :
    inner ℝ u (matrixOperator A u) =
      RCLike.re (dotProduct (star ⇑u) (A.mulVec ⇑u)) := by
  change RCLike.re (inner ℂ u (A.toEuclideanLin u)) = _
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
    dotProduct_comm]

theorem matrixOperator_lower_bound {A : InternalMatrix N} {δ : ℝ}
    (hA : HasMatrixLowerBound A δ) : HasOperatorLowerBound (matrixOperator A) δ := by
  intro u
  have h := hA.re_dotProduct_nonneg ⇑u
  simp only [realScalarMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, map_sub, smul_eq_mul, RCLike.mul_re] at h
  have hrRe : RCLike.re (δ : ℂ) = δ := rfl
  have hrIm : RCLike.im (δ : ℂ) = 0 := rfl
  rw [hrRe, hrIm, zero_mul, sub_zero] at h
  have hnorm : RCLike.re (dotProduct (star ⇑u) ⇑u) = ‖u‖ ^ 2 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [hnorm] at h
  rw [matrixOperator_quadratic]
  linarith

theorem matrix_oscillator_exists_unique (A : InternalMatrix N) (δ : ℝ)
    (hA : HasMatrixLowerBound A δ) (hδ : 0 < δ) (u0 v0 : InternalHilbert N) :
    ∃! z : ℝ → InternalHilbert N × InternalHilbert N,
      z 0 = (u0, v0) ∧
        IsOscillator (matrixOperator A) (fun t => (z t).1) (fun t => (z t).2) :=
  global_solution_exists_unique (matrixOperator A)
    (matrixOperator_symmetric (MassMatrix.hermitian_of_lower_bound hA)) δ hδ
    (matrixOperator_lower_bound hA) u0 v0

theorem matrix_stability_bound (A : InternalMatrix N) (δ : ℝ)
    (hA : HasMatrixLowerBound A δ) (u v : ℝ → InternalHilbert N)
    (h : IsOscillator (matrixOperator A) u v) (t : ℝ) :
    ‖v t‖ ^ 2 + δ * ‖u t‖ ^ 2 ≤ 2 * energy (matrixOperator A) (u 0) (v 0) :=
  stability_bound (matrixOperator A)
    (matrixOperator_symmetric (MassMatrix.hermitian_of_lower_bound hA)) δ
    (matrixOperator_lower_bound hA) u v h t

def waveNumberSquared (k : SpatialMomenta) : ℝ := ∑ j : SpatialIndex, (k j) ^ 2

theorem waveNumberSquared_nonneg (k : SpatialMomenta) : 0 ≤ waveNumberSquared k :=
  Finset.sum_nonneg (fun j _ => sq_nonneg (k j))

/-- 一定のM²に対する波数ごとの行列。フーリエ変換自体の構成ではない。 -/
def waveMatrix (M : InternalMatrix N) (k : SpatialMomenta) : InternalMatrix N :=
  realScalarMatrix (waveNumberSquared k) + M

theorem waveMatrix_lower_bound (M : InternalMatrix N) (k : SpatialMomenta) (δ : ℝ)
    (hM : HasMatrixLowerBound M δ) :
    HasMatrixLowerBound (waveMatrix M k) (waveNumberSquared k + δ) := by
  unfold HasMatrixLowerBound waveMatrix
  rw [MassMatrix.scalarMatrix_add]
  have heq : realScalarMatrix (waveNumberSquared k) + M -
      (realScalarMatrix (waveNumberSquared k) + realScalarMatrix δ) =
      M - realScalarMatrix δ := by abel
  rw [heq]
  exact hM

theorem freeMode_exists_unique (M : InternalMatrix N) (k : SpatialMomenta) (δ : ℝ)
    (hM : HasMatrixLowerBound M δ) (hδ : 0 < δ) (u0 v0 : InternalHilbert N) :
    ∃! z : ℝ → InternalHilbert N × InternalHilbert N,
      z 0 = (u0, v0) ∧ IsOscillator (matrixOperator (waveMatrix M k))
        (fun t => (z t).1) (fun t => (z t).2) := by
  exact matrix_oscillator_exists_unique (waveMatrix M k) (waveNumberSquared k + δ)
    (waveMatrix_lower_bound M k δ hM) (add_pos_of_nonneg_of_pos (waveNumberSquared_nonneg k) hδ)
    u0 v0

theorem freeMode_stability_bound (M : InternalMatrix N) (k : SpatialMomenta) (δ : ℝ)
    (hM : HasMatrixLowerBound M δ) (u v : ℝ → InternalHilbert N)
    (h : IsOscillator (matrixOperator (waveMatrix M k)) u v) (t : ℝ) :
    ‖v t‖ ^ 2 + (waveNumberSquared k + δ) * ‖u t‖ ^ 2 ≤
      2 * energy (matrixOperator (waveMatrix M k)) (u 0) (v 0) :=
  matrix_stability_bound (waveMatrix M k) (waveNumberSquared k + δ)
    (waveMatrix_lower_bound M k δ hM) u v h t

/-- a=3、μ=1、零相互作用、具体的な巡回シフトから作る自由質量行列。 -/
def referenceFreeMass (N : ℕ) [NeZero N] : InternalMatrix N :=
  freeMassSquared referenceParameters (Lattice.concreteInternalShifts N)

theorem referenceFreeMass_lower_bound :
    HasMatrixLowerBound (referenceFreeMass N) (1 / 9) := by
  simpa only [referenceFreeMass, massSquared, zeroPotential, add_zero] using
    MassMatrix.reference_mass_lower_bound (Lattice.concreteInternalShifts N) zeroPotential
      (fun _ _ => Matrix.PosSemidef.zero) 0 (fun _ => 0)

theorem reference_freeMode_exists_unique (k : SpatialMomenta) (u0 v0 : InternalHilbert N) :
    ∃! z : ℝ → InternalHilbert N × InternalHilbert N,
      z 0 = (u0, v0) ∧ IsOscillator (matrixOperator (waveMatrix (referenceFreeMass N) k))
        (fun t => (z t).1) (fun t => (z t).2) :=
  freeMode_exists_unique (referenceFreeMass N) k (1 / 9) referenceFreeMass_lower_bound
    (by norm_num) u0 v0

theorem reference_freeMode_stability (k : SpatialMomenta) (u v : ℝ → InternalHilbert N)
    (h : IsOscillator (matrixOperator (waveMatrix (referenceFreeMass N) k)) u v) (t : ℝ) :
    ‖v t‖ ^ 2 + (waveNumberSquared k + 1 / 9) * ‖u t‖ ^ 2 ≤
      2 * energy (matrixOperator (waveMatrix (referenceFreeMass N) k)) (u 0) (v 0) :=
  freeMode_stability_bound (referenceFreeMass N) k (1 / 9) referenceFreeMass_lower_bound u v h t

end MatrixOscillators

/-! ## 7.3　非有界作用素の定義域上での、強解に対する条件付き評価 -/

section DomainStrongSolutions
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 定義域D上での対称性。自己共役性や最大定義域を仮定・証明したものではない。 -/
def DomainSymmetric (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) : Prop :=
  ∀ u v : D, inner ℝ (A u) (v : E) = inner ℝ (u : E) (A v)

def DomainLowerBound (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) (δ : ℝ) : Prop :=
  ∀ u : D, δ * ‖(u : E)‖ ^ 2 ≤ inner ℝ (u : E) (A u)

/--
Dに属するu,vと、環境ヒルベルト空間Eでの微分条件。
第三条件 (Au)'=Av は、非有界Aと時間微分を交換できるための
追加の正則性条件であり、u'=vだけから自動的には導かれない。
これらの条件から保存則を導くが、そのような解の存在はここでは証明しない。
-/
def IsStrongDomainWave (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) (u v : ℝ → D) : Prop :=
  ∀ t, HasDerivAt (fun s => (u s : E)) (v t : E) t ∧
    HasDerivAt (fun s => (v s : E)) (-(A (u t))) t ∧
    HasDerivAt (fun s => A (u s)) (A (v t)) t

def domainEnergy (D : Submodule ℝ E) (A : D →ₗ[ℝ] E) (u v : D) : ℝ :=
  (‖(v : E)‖ ^ 2 + inner ℝ (u : E) (A u)) / 2

theorem domain_energy_hasDerivAt_zero (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (hA : DomainSymmetric D A) (u v : ℝ → D) (h : IsStrongDomainWave D A u v) (t : ℝ) :
    HasDerivAt (fun s => domainEnergy D A (u s) (v s)) 0 t := by
  have hd := ((h t).2.1.norm_sq.add ((h t).1.inner ℝ (h t).2.2)).div_const 2
  have hz : (2 * inner ℝ (v t : E) (-(A (u t))) +
      (inner ℝ (u t : E) (A (v t)) + inner ℝ (v t : E) (A (u t)))) / 2 = 0 := by
    rw [inner_neg_right, ← hA (u t) (v t), real_inner_comm (A (u t)) (v t : E)]
    ring
  change HasDerivAt (fun s => domainEnergy D A (u s) (v s))
    ((2 * inner ℝ (v t : E) (-(A (u t))) +
      (inner ℝ (u t : E) (A (v t)) + inner ℝ (v t : E) (A (u t)))) / 2) t at hd
  rw [hz] at hd
  exact hd

theorem domain_energy_conserved (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (hA : DomainSymmetric D A) (u v : ℝ → D) (h : IsStrongDomainWave D A u v) (t s : ℝ) :
    domainEnergy D A (u t) (v t) = domainEnergy D A (u s) (v s) :=
  is_const_of_deriv_eq_zero
    (fun r => (domain_energy_hasDerivAt_zero D A hA u v h r).differentiableAt)
    (fun r => (domain_energy_hasDerivAt_zero D A hA u v h r).deriv) t s

theorem domain_stability_bound (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (hA : DomainSymmetric D A) (δ : ℝ) (hLower : DomainLowerBound D A δ)
    (u v : ℝ → D) (h : IsStrongDomainWave D A u v) (t : ℝ) :
    ‖(v t : E)‖ ^ 2 + δ * ‖(u t : E)‖ ^ 2 ≤ 2 * domainEnergy D A (u 0) (v 0) := by
  rw [← domain_energy_conserved D A hA u v h t 0]
  have hb := hLower (u t)
  dsimp [domainEnergy]
  linarith

end DomainStrongSolutions
/-!
## 7.4　証明範囲と残る解析課題

本ファイルで機械検証すること：

* oscillator_secondOrder：一階化した方程式からu''+Au=0。
* energy_hasDerivAt_zero / energy_conserved：対称な静的Aに対する保存則。
* stability_bound / stability_bounds_separate：エネルギーによる一様評価。
* difference_stability_bound / oscillator_unique：初期値の差の評価と一意性。
* flow / flow_isOscillator / global_solution_exists_unique：有界Aの大域解の構成。
* matrixOperator_symmetric / matrixOperator_lower_bound：第五章との接続。
* matrix_oscillator_exists_unique / matrix_stability_bound：有限成分の初期値問題。
* waveMatrix_lower_bound / freeMode_exists_unique / freeMode_stability_bound：各波数の評価。
* reference_freeMode_exists_unique / reference_freeMode_stability：任意Nでの参照模型。
* domain_energy_conserved / domain_stability_bound：指定した正則な強解の保存則と評価。

空間連続の場について残る課題：

1. L²上の-Δと行列値V(x)から、作用素Aとその定義域を実際に構成する。
2. 境界条件・有限エネルギー条件の下で、自己共役性と下界を証明する。
3. 強解の存在を構成し、有限エネルギー初期値へ延長する。
4. フーリエ変換の等長性、積分、極限を正当化して場のエネルギー評価へ移す。
5. 正周波数発展を主張する場合は、√Aと対応するユニタリ群を別に構成する。

7.3のDやAは任意の入力であり、名前を付けただけで空間微分作用素を
実現したとは扱わない。有界Aの指数作用素による存在証明を、非有界な
-Δ+M²(x)へそのまま適用することもしない。

本章の結果から、非線形安定性、独立した三時間発展の整合性、
散乱行列のユニタリティ、完全な量子場理論の安定性までは結論しない。
-/

#print axioms oscillator_secondOrder
#print axioms energy_conserved
#print axioms stability_bounds_separate
#print axioms difference_stability_bound
#print axioms global_solution_exists_unique
#print axioms matrixOperator_lower_bound
#print axioms matrix_oscillator_exists_unique
#print axioms freeMode_stability_bound
#print axioms reference_freeMode_exists_unique
#print axioms reference_freeMode_stability
#print axioms domain_energy_conserved
#print axioms domain_stability_bound

end EnergyStability
end TwelveDimensionalPhaseSpace
