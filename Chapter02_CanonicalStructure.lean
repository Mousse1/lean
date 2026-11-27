import Chapter01_Definitions
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# 第二章　12次元正準構造と質量殻制約

第一章のPhasePoint上の定数係数正準2形式と、
12変数の実多項式上の正準ポアソン括弧を構成する。
一般の滑らかな関数全体へのポアソン代数の拡張は主張しない。

第一章のファイルを同じmathlibプロジェクトに置く。
第一章のコンパイル済みモジュールがまだない場合のコマンド例：

    lake env lean -o .lake/build/lib/lean/Chapter01_Definitions.olean Chapter01_Definitions.lean
    lake env lean -DwarningAsError=true Chapter02_CanonicalStructure.lean

本章では、定数係数形式の閉性・非退化性、多項式ポアソン括弧の
Jacobi恒等式、質量殻保存、対称性を仮定した共役量の保存まで扱う。
軌道の存在、一般多様体への拡張、独立した三時間発展は結論に含めない。

## 検証記録

Lean 4.24.0 / mathlib v4.24.0でコンパイル確認済み。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
警告をエラーとして扱うコマンドで終了コード0。
末尾で確認する主要定理の公理依存は、
propext、Classical.choice、Quot.soundのみ。
第一章の定義を変更した場合、第一章と本章を順に再コンパイルする。
-/

noncomputable section
open scoped BigOperators

namespace TwelveDimensionalPhaseSpace
namespace Canonical

abbrev ConfigurationIndex := SpatialIndex ⊕ TemporalIndex
abbrev CanonicalIndex := ConfigurationIndex ⊕ ConfigurationIndex
abbrev PhasePolynomial := MvPolynomial CanonicalIndex ℝ
abbrev ConfigurationPolynomial := MvPolynomial ConfigurationIndex ℝ

def qValue (z : PhasePoint) : ConfigurationIndex → ℝ :=
  Sum.elim z.1.1 z.1.2

def pValue (z : PhasePoint) : ConfigurationIndex → ℝ :=
  Sum.elim z.2.1 z.2.2

def phaseValues (z : PhasePoint) : CanonicalIndex → ℝ :=
  Sum.elim (qValue z) (pValue z)

def phaseFromValues (q p : ConfigurationIndex → ℝ) : PhasePoint :=
  ((q ∘ Sum.inl, q ∘ Sum.inr), (p ∘ Sum.inl, p ∘ Sum.inr))

@[simp] theorem qValue_phaseFromValues (q p : ConfigurationIndex → ℝ)
    (i : ConfigurationIndex) : qValue (phaseFromValues q p) i = q i := by
  cases i <;> rfl

@[simp] theorem pValue_phaseFromValues (q p : ConfigurationIndex → ℝ)
    (i : ConfigurationIndex) : pValue (phaseFromValues q p) i = p i := by
  cases i <;> rfl

@[simp] theorem qValue_add (u v : PhasePoint) (i : ConfigurationIndex) :
    qValue (u + v) i = qValue u i + qValue v i := by
  cases i <;> rfl

@[simp] theorem pValue_add (u v : PhasePoint) (i : ConfigurationIndex) :
    pValue (u + v) i = pValue u i + pValue v i := by
  cases i <;> rfl

@[simp] theorem qValue_smul (r : ℝ) (u : PhasePoint) (i : ConfigurationIndex) :
    qValue (r • u) i = r * qValue u i := by
  cases i <;> rfl

@[simp] theorem pValue_smul (r : ℝ) (u : PhasePoint) (i : ConfigurationIndex) :
    pValue (r • u) i = r * pValue u i := by
  cases i <;> rfl

/-! ## 2.1　正準2形式 -/

/-- Ω(u,v)=Σ(dq∧dp)(u,v)。時間方向も正準運動量Pを用いる。 -/
def canonicalOmega (u v : PhasePoint) : ℝ :=
  ∑ i, (qValue u i * pValue v i - pValue u i * qValue v i)

theorem omega_add_left (u v w : PhasePoint) :
    canonicalOmega (u + v) w = canonicalOmega u w + canonicalOmega v w := by
  simp only [canonicalOmega, qValue_add, pValue_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem omega_add_right (u v w : PhasePoint) :
    canonicalOmega u (v + w) = canonicalOmega u v + canonicalOmega u w := by
  simp only [canonicalOmega, qValue_add, pValue_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem omega_smul_left (r : ℝ) (u v : PhasePoint) :
    canonicalOmega (r • u) v = r * canonicalOmega u v := by
  simp only [canonicalOmega, qValue_smul, pValue_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem omega_smul_right (r : ℝ) (u v : PhasePoint) :
    canonicalOmega u (r • v) = r * canonicalOmega u v := by
  simp only [canonicalOmega, qValue_smul, pValue_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem omega_skew (u v : PhasePoint) :
    canonicalOmega u v = -canonicalOmega v u := by
  simp only [canonicalOmega]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem omega_alternating (u : PhasePoint) : canonicalOmega u u = 0 := by
  simp [canonicalOmega, mul_comm]

/-- 正準形式を実双線形形式として束ねる。 -/
def canonicalBilinear : PhasePoint →ₗ[ℝ] PhasePoint →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := canonicalOmega u
      map_add' := omega_add_right u
      map_smul' := fun r v => omega_smul_right r u v }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    exact omega_add_left u v w
  map_smul' r u := by
    apply LinearMap.ext
    intro v
    exact omega_smul_left r u v

/-- Ω(u,v)=0が全vについて成立するならu=0。 -/
theorem omega_nondegenerate (u : PhasePoint)
    (h : ∀ v, canonicalOmega u v = 0) : u = 0 := by
  classical
  have hq (i : ConfigurationIndex) : qValue u i = 0 := by
    have hv := h (phaseFromValues 0 (Pi.single i 1))
    simpa [canonicalOmega, Pi.single_apply, mul_ite, ite_mul] using hv
  have hp (i : ConfigurationIndex) : pValue u i = 0 := by
    have hv := h (phaseFromValues (Pi.single i 1) 0)
    have hn : -pValue u i = 0 := by
      simpa [canonicalOmega, Pi.single_apply, mul_ite, ite_mul] using hv
    exact neg_eq_zero.mp hn
  apply Prod.ext
  · apply Prod.ext
    · funext i
      exact hq (Sum.inl i)
    · funext a
      exact hq (Sum.inr a)
  · apply Prod.ext
    · funext i
      exact hp (Sum.inl i)
    · funext a
      exact hp (Sum.inr a)

/-- 平坦な相空間上で、各点に同じ双線形形式を置く。 -/
def canonicalFormAt (_z : PhasePoint) (u v : PhasePoint) : ℝ :=
  canonicalOmega u v

/--
定ベクトル場u,v,wで評価した外微分の座標式。
点への依存には実際のFréchet微分を用い、閉性を仮定しない。
-/
def canonicalExteriorDerivative (z u v w : PhasePoint) : ℝ :=
  (fderiv ℝ (fun y => canonicalFormAt y v w) z) u -
    (fderiv ℝ (fun y => canonicalFormAt y u w) z) v +
    (fderiv ℝ (fun y => canonicalFormAt y u v) z) w

theorem canonicalForm_closed (z u v w : PhasePoint) :
    canonicalExteriorDerivative z u v w = 0 := by
  simp [canonicalExteriorDerivative, canonicalFormAt]

/-- 係数関数の滑らかさ。閉性計算の対象が滑らかな定数係数形式である。 -/
theorem canonicalForm_smooth (u v : PhasePoint) :
    ContDiff ℝ ⊤ (fun z : PhasePoint => canonicalFormAt z u v) :=
  contDiff_const

/-! ## 2.2　実多項式上の正準ポアソン括弧 -/

def qPolynomial (i : ConfigurationIndex) : PhasePolynomial :=
  MvPolynomial.X (Sum.inl i)

def pPolynomial (i : ConfigurationIndex) : PhasePolynomial :=
  MvPolynomial.X (Sum.inr i)

def poissonBracket (f g : PhasePolynomial) : PhasePolynomial :=
  ∑ i, (MvPolynomial.pderiv (Sum.inl i) f * MvPolynomial.pderiv (Sum.inr i) g -
    MvPolynomial.pderiv (Sum.inr i) f * MvPolynomial.pderiv (Sum.inl i) g)

theorem poisson_skew (f g : PhasePolynomial) :
    poissonBracket f g = -poissonBracket g f := by
  unfold poissonBracket
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem poisson_self (f : PhasePolynomial) : poissonBracket f f = 0 := by
  simp [poissonBracket, mul_comm]

theorem poisson_add_left (f g h : PhasePolynomial) :
    poissonBracket (f + g) h = poissonBracket f h + poissonBracket g h := by
  simp only [poissonBracket, map_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem poisson_add_right (f g h : PhasePolynomial) :
    poissonBracket f (g + h) = poissonBracket f g + poissonBracket f h := by
  simp only [poissonBracket, map_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem poisson_neg_right (f g : PhasePolynomial) :
    poissonBracket f (-g) = -poissonBracket f g := by
  simp only [poissonBracket, map_neg]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem poisson_neg_left (f g : PhasePolynomial) :
    poissonBracket (-f) g = -poissonBracket f g := by
  rw [poisson_skew (-f) g, poisson_neg_right, neg_neg, poisson_skew g f]

theorem poisson_mul_left (f g h : PhasePolynomial) :
    poissonBracket (f * g) h =
      poissonBracket f h * g + f * poissonBracket g h := by
  simp only [poissonBracket, MvPolynomial.pderiv_mul, Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem poisson_mul_right (f g h : PhasePolynomial) :
    poissonBracket f (g * h) =
      poissonBracket f g * h + g * poissonBracket f h := by
  simp only [poissonBracket, MvPolynomial.pderiv_mul, Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem poisson_C_left (r : ℝ) (f : PhasePolynomial) :
    poissonBracket (MvPolynomial.C r) f = 0 := by
  simp [poissonBracket]

@[simp] theorem poisson_C_right (f : PhasePolynomial) (r : ℝ) :
    poissonBracket f (MvPolynomial.C r) = 0 := by
  simp [poissonBracket]

theorem poisson_C_mul_left (r : ℝ) (f g : PhasePolynomial) :
    poissonBracket (MvPolynomial.C r * f) g = MvPolynomial.C r * poissonBracket f g := by
  rw [poisson_mul_left, poisson_C_left, zero_mul, zero_add]

theorem poisson_C_mul_right (r : ℝ) (f g : PhasePolynomial) :
    poissonBracket f (MvPolynomial.C r * g) = MvPolynomial.C r * poissonBracket f g := by
  rw [poisson_mul_right, poisson_C_right, zero_mul, zero_add]

@[simp] theorem poisson_q_left (i : ConfigurationIndex) (f : PhasePolynomial) :
    poissonBracket (qPolynomial i) f = MvPolynomial.pderiv (Sum.inr i) f := by
  classical
  simp [poissonBracket, qPolynomial, MvPolynomial.pderiv_X,
    Pi.single_apply, ite_mul]

@[simp] theorem poisson_p_left (i : ConfigurationIndex) (f : PhasePolynomial) :
    poissonBracket (pPolynomial i) f = -MvPolynomial.pderiv (Sum.inl i) f := by
  classical
  simp [poissonBracket, pPolynomial, MvPolynomial.pderiv_X,
    Pi.single_apply, ite_mul, Finset.sum_neg_distrib]

@[simp] theorem poisson_q_right (f : PhasePolynomial) (i : ConfigurationIndex) :
    poissonBracket f (qPolynomial i) = -MvPolynomial.pderiv (Sum.inr i) f := by
  rw [poisson_skew, poisson_q_left]

@[simp] theorem poisson_p_right (f : PhasePolynomial) (i : ConfigurationIndex) :
    poissonBracket f (pPolynomial i) = MvPolynomial.pderiv (Sum.inl i) f := by
  rw [poisson_skew, poisson_p_left, neg_neg]

theorem poisson_q_p (i j : ConfigurationIndex) :
    poissonBracket (qPolynomial i) (pPolynomial j) = if i = j then 1 else 0 := by
  classical
  simp [pPolynomial, MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

theorem poisson_q_q (i j : ConfigurationIndex) :
    poissonBracket (qPolynomial i) (qPolynomial j) = 0 := by
  rw [poisson_q_left]
  simp [qPolynomial, MvPolynomial.pderiv_X]

theorem poisson_p_p (i j : ConfigurationIndex) :
    poissonBracket (pPolynomial i) (pPolynomial j) = 0 := by
  rw [poisson_p_left]
  simp [pPolynomial, MvPolynomial.pderiv_X]

@[simp] theorem poisson_X_right (f : PhasePolynomial) (k : CanonicalIndex) :
    poissonBracket f (MvPolynomial.X k) =
      Sum.elim (fun i => -MvPolynomial.pderiv (Sum.inr i) f)
        (fun i => MvPolynomial.pderiv (Sum.inl i) f) k := by
  cases k with
  | inl i => exact poisson_q_right f i
  | inr i => exact poisson_p_right f i

/-- 混合形式微分の交換性を、導分の交換子と多項式生成元上の計算から導く。 -/
theorem pderiv_commute (i j : CanonicalIndex) (f : PhasePolynomial) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  have hz : ⁅(MvPolynomial.pderiv i : Derivation ℝ PhasePolynomial PhasePolynomial),
      (MvPolynomial.pderiv j : Derivation ℝ PhasePolynomial PhasePolynomial)⁆ =
      (0 : Derivation ℝ PhasePolynomial PhasePolynomial) := by
    apply MvPolynomial.derivation_ext
    intro k
    by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp [Derivation.commutator_apply, MvPolynomial.pderiv_X, hi, hj]
  have h := congrArg (fun D : Derivation ℝ PhasePolynomial PhasePolynomial => D f) hz
  exact sub_eq_zero.mp (by simpa [Derivation.commutator_apply] using h)

theorem pderiv_poisson (k : CanonicalIndex) (f g : PhasePolynomial) :
    MvPolynomial.pderiv k (poissonBracket f g) =
      poissonBracket (MvPolynomial.pderiv k f) g +
        poissonBracket f (MvPolynomial.pderiv k g) := by
  simp only [poissonBracket, map_sum, map_sub, MvPolynomial.pderiv_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pderiv_commute k (Sum.inl i) f, pderiv_commute k (Sum.inr i) f,
    pderiv_commute k (Sum.inl i) g, pderiv_commute k (Sum.inr i) g]
  ring

/--
fを左引数に固定した導分。これは物理的な時間発展{G,H}とは引数の順が逆である。
Jacobi恒等式の証明のために用いる。
-/
def leftPoissonDerivation (f : PhasePolynomial) :
    Derivation ℝ PhasePolynomial PhasePolynomial :=
  MvPolynomial.mkDerivation ℝ
    (Sum.elim (fun i => -MvPolynomial.pderiv (Sum.inr i) f)
      (fun i => MvPolynomial.pderiv (Sum.inl i) f))

theorem leftPoissonDerivation_apply (f g : PhasePolynomial) :
    leftPoissonDerivation f g = poissonBracket f g := by
  induction g using MvPolynomial.induction_on with
  | C r => simp [leftPoissonDerivation]
  | add g h hg hh => simp [map_add, hg, hh, poisson_add_right]
  | mul_X g i hg =>
    rw [Derivation.leibniz, poisson_mul_right, hg]
    simp [leftPoissonDerivation, smul_eq_mul, mul_comm, add_comm]

theorem leftPoissonDerivation_commutator (f g : PhasePolynomial) :
    ⁅leftPoissonDerivation f, leftPoissonDerivation g⁆ =
      leftPoissonDerivation (poissonBracket f g) := by
  apply MvPolynomial.derivation_ext
  intro k
  cases k with
  | inl i =>
    simp only [Derivation.commutator_apply, leftPoissonDerivation_apply,
      poisson_X_right, Sum.elim_inl, poisson_neg_right, pderiv_poisson]
    rw [poisson_skew g (MvPolynomial.pderiv (Sum.inr i) f)]
    ring
  | inr i =>
    simp only [Derivation.commutator_apply, leftPoissonDerivation_apply,
      poisson_X_right, Sum.elim_inr, pderiv_poisson]
    rw [poisson_skew g (MvPolynomial.pderiv (Sum.inl i) f)]
    ring

theorem poisson_jacobi_leibniz (f g h : PhasePolynomial) :
    poissonBracket f (poissonBracket g h) =
      poissonBracket (poissonBracket f g) h + poissonBracket g (poissonBracket f h) := by
  have hc := congrArg (fun D : Derivation ℝ PhasePolynomial PhasePolynomial => D h)
    (leftPoissonDerivation_commutator f g)
  have he : poissonBracket f (poissonBracket g h) -
      poissonBracket g (poissonBracket f h) = poissonBracket (poissonBracket f g) h := by
    simpa only [Derivation.commutator_apply, leftPoissonDerivation_apply] using hc
  exact sub_eq_iff_eq_add.mp he

/-- 循環和で表したJacobi恒等式。混合微分の交換性まで遡って証明する。 -/
theorem poisson_jacobi (f g h : PhasePolynomial) :
    poissonBracket f (poissonBracket g h) +
      poissonBracket g (poissonBracket h f) +
      poissonBracket h (poissonBracket f g) = 0 := by
  have h2 : poissonBracket g (poissonBracket h f) =
      -poissonBracket g (poissonBracket f h) := by
    rw [poisson_skew h f, poisson_neg_right]
  rw [poisson_jacobi_leibniz, h2, poisson_skew h (poissonBracket f g)]
  ring

/-- 第一章の実相空間上で多項式を評価する。 -/
def evalAt (f : PhasePolynomial) (z : PhasePoint) : ℝ :=
  MvPolynomial.eval (phaseValues z) f

def hamiltonianVector (H : PhasePolynomial) (z : PhasePoint) : PhasePoint :=
  phaseFromValues
    (fun i => evalAt (MvPolynomial.pderiv (Sum.inr i) H) z)
    (fun i => -evalAt (MvPolynomial.pderiv (Sum.inl i) H) z)

/-- 多項式の形式偏微分から定まる方向微分の成分式。 -/
def polynomialDifferential (H : PhasePolynomial) (z v : PhasePoint) : ℝ :=
  ∑ i, (evalAt (MvPolynomial.pderiv (Sum.inl i) H) z * qValue v i +
    evalAt (MvPolynomial.pderiv (Sum.inr i) H) z * pValue v i)

theorem omega_hamiltonianVector (H : PhasePolynomial) (z v : PhasePoint) :
    canonicalOmega (hamiltonianVector H z) v = polynomialDifferential H z v := by
  simp only [canonicalOmega, hamiltonianVector, qValue_phaseFromValues,
    pValue_phaseFromValues, polynomialDifferential]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem evalAt_poisson (f g : PhasePolynomial) (z : PhasePoint) :
    evalAt (poissonBracket f g) z =
      ∑ i, (evalAt (MvPolynomial.pderiv (Sum.inl i) f) z *
        evalAt (MvPolynomial.pderiv (Sum.inr i) g) z -
        evalAt (MvPolynomial.pderiv (Sum.inr i) f) z *
        evalAt (MvPolynomial.pderiv (Sum.inl i) g) z) := by
  simp [evalAt, poissonBracket]

theorem poisson_as_hamiltonian_direction (f H : PhasePolynomial) (z : PhasePoint) :
    evalAt (poissonBracket f H) z =
      polynomialDifferential f z (hamiltonianVector H z) := by
  rw [evalAt_poisson]
  simp only [polynomialDifferential, hamiltonianVector,
    qValue_phaseFromValues, pValue_phaseFromValues]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## 2.3　質量殻制約と共役量の保存条件 -/

def liftConfiguration (V : ConfigurationPolynomial) : PhasePolynomial :=
  MvPolynomial.rename Sum.inl V

def metricSign : ConfigurationIndex → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => -1)

def kineticPolynomial : PhasePolynomial :=
  ∑ i, MvPolynomial.C (metricSign i) * pPolynomial i ^ 2

/-- 符号数(3,3)の質量殻。Vは座標だけに依存する実多項式。 -/
def massShellPolynomial (μ : ℝ) (V : ConfigurationPolynomial) : PhasePolynomial :=
  MvPolynomial.C (1 / 2 : ℝ) *
    (kineticPolynomial + MvPolynomial.C (μ ^ 2) + liftConfiguration V)

theorem kineticPolynomial_spatial_temporal :
    kineticPolynomial =
      (∑ i : SpatialIndex, pPolynomial (Sum.inl i) ^ 2) -
        ∑ a : TemporalIndex, pPolynomial (Sum.inr a) ^ 2 := by
  simp [kineticPolynomial, metricSign, Fintype.sum_sum_type, sub_eq_add_neg]

theorem massShell_expanded (μ : ℝ) (V : ConfigurationPolynomial) :
    massShellPolynomial μ V =
      MvPolynomial.C (1 / 2 : ℝ) *
        ((∑ i : SpatialIndex, pPolynomial (Sum.inl i) ^ 2) +
          MvPolynomial.C (μ ^ 2) + liftConfiguration V -
          ∑ a : TemporalIndex, pPolynomial (Sum.inr a) ^ 2) := by
  rw [massShellPolynomial, kineticPolynomial_spatial_temporal]
  ring

theorem qderiv_kinetic_zero (i : ConfigurationIndex) :
    MvPolynomial.pderiv (Sum.inl i) kineticPolynomial = 0 := by
  simp [kineticPolynomial, pPolynomial, MvPolynomial.pderiv_X]

theorem qderiv_lift (i : ConfigurationIndex) (V : ConfigurationPolynomial) :
    MvPolynomial.pderiv (Sum.inl i) (liftConfiguration V) =
      liftConfiguration (MvPolynomial.pderiv i V) :=
  MvPolynomial.pderiv_rename Sum.inl_injective i V

theorem qderiv_massShell (i : ConfigurationIndex) (μ : ℝ)
    (V : ConfigurationPolynomial) :
    MvPolynomial.pderiv (Sum.inl i) (massShellPolynomial μ V) =
      MvPolynomial.C (1 / 2 : ℝ) * liftConfiguration (MvPolynomial.pderiv i V) := by
  simp [massShellPolynomial, qderiv_kinetic_zero, qderiv_lift]

/-- 世界線パラメータごとのeは相空間上の定数であり、相空間依存の乗数は扱わない。 -/
def constrainedRate (e : ℝ) (C f : PhasePolynomial) : PhasePolynomial :=
  poissonBracket f (MvPolynomial.C e * C)

theorem constraint_rate_zero (e : ℝ) (C : PhasePolynomial) :
    constrainedRate e C C = 0 := by
  rw [constrainedRate, poisson_C_mul_right, poisson_self, mul_zero]

theorem momentum_rate (e μ : ℝ) (V : ConfigurationPolynomial)
    (i : ConfigurationIndex) :
    constrainedRate e (massShellPolynomial μ V) (pPolynomial i) =
      -(MvPolynomial.C (e / 2) * liftConfiguration (MvPolynomial.pderiv i V)) := by
  rw [constrainedRate, poisson_C_mul_right, poisson_p_left, qderiv_massShell]
  have hc : (MvPolynomial.C (e / 2) : PhasePolynomial) =
      MvPolynomial.C e * MvPolynomial.C (1 / 2 : ℝ) := by
    rw [show e / 2 = e * (1 / 2 : ℝ) by ring, map_mul]
  rw [hc]
  ring

/-- Vの対応する座標微分が消えるとき、共役運動量の変化率がゼロになる。 -/
theorem momentum_rate_zero_of_translation_invariant (e μ : ℝ)
    (V : ConfigurationPolynomial) (i : ConfigurationIndex)
    (hV : MvPolynomial.pderiv i V = 0) :
    constrainedRate e (massShellPolynomial μ V) (pPolynomial i) = 0 := by
  rw [momentum_rate, hV]
  simp [liftConfiguration]

theorem temporalMomentum_rate (e μ : ℝ) (V : ConfigurationPolynomial)
    (a : TemporalIndex) :
    constrainedRate e (massShellPolynomial μ V) (pPolynomial (Sum.inr a)) =
      -(MvPolynomial.C (e / 2) *
        liftConfiguration (MvPolynomial.pderiv (Sum.inr a) V)) :=
  momentum_rate e μ V (Sum.inr a)

/-- 第一章のP_a=-E_aに対応するエネルギー多項式。 -/
def temporalEnergyPolynomial (a : TemporalIndex) : PhasePolynomial :=
  -pPolynomial (Sum.inr a)

theorem evalAt_temporalEnergy (a : TemporalIndex) (z : PhasePoint) :
    evalAt (temporalEnergyPolynomial a) z = temporalEnergy z a := by
  simp [evalAt, temporalEnergyPolynomial, pPolynomial, phaseValues,
    pValue, temporalEnergy]

/-- P=-Eの規約では{t,E}=-δとなる。正準対は(t,P)である。 -/
theorem poisson_time_energy (a b : TemporalIndex) :
    poissonBracket (qPolynomial (Sum.inr a)) (temporalEnergyPolynomial b) =
      -(if a = b then 1 else 0) := by
  rw [temporalEnergyPolynomial, poisson_neg_right, poisson_q_p]
  simp

theorem temporalEnergy_rate (e μ : ℝ) (V : ConfigurationPolynomial)
    (a : TemporalIndex) :
    constrainedRate e (massShellPolynomial μ V) (temporalEnergyPolynomial a) =
      MvPolynomial.C (e / 2) *
        liftConfiguration (MvPolynomial.pderiv (Sum.inr a) V) := by
  change poissonBracket (-pPolynomial (Sum.inr a))
    (MvPolynomial.C e * massShellPolynomial μ V) = _
  rw [poisson_neg_left]
  change -constrainedRate e (massShellPolynomial μ V)
    (pPolynomial (Sum.inr a)) = _
  rw [temporalMomentum_rate, neg_neg]

/-- 反例：時間座標に線形依存するVでは、Cは保存されてもP_aの変化率は非零。 -/
theorem linear_time_potential_momentum_rate (μ : ℝ) (a : TemporalIndex) :
    constrainedRate 1 (massShellPolynomial μ (MvPolynomial.X (Sum.inr a)))
      (pPolynomial (Sum.inr a)) = MvPolynomial.C (-1 / 2 : ℝ) := by
  rw [momentum_rate]
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, map_neg]
  simp [liftConfiguration]

theorem linear_time_potential_momentum_rate_ne_zero (μ : ℝ) (a : TemporalIndex) :
    constrainedRate 1 (massShellPolynomial μ (MvPolynomial.X (Sum.inr a)))
      (pPolynomial (Sum.inr a)) ≠ 0 := by
  rw [linear_time_potential_momentum_rate]
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : CanonicalIndex => (0 : ℝ))) h
  norm_num at he

/-!
### 多項式の変化率を、実際の軌道に沿う微分へ接続する

IsHamiltonTrajectoryは座標ごとのHamilton方程式を仮定する。
保存量そのものを軌道の定義に含めず、任意の多項式についての連鎖律を
生成元・和・積から導く。軌道の存在はこの章の結論には含まれない。
-/

def IsHamiltonTrajectory (H : PhasePolynomial) (e : ℝ → ℝ)
    (γ : ℝ → PhasePoint) : Prop :=
  ∀ sParam i, HasDerivAt (fun t => evalAt (MvPolynomial.X i) (γ t))
    (evalAt (constrainedRate (e sParam) H (MvPolynomial.X i)) (γ sParam)) sParam

theorem hasDerivAt_eval_along_hamiltonian (H : PhasePolynomial)
    (e : ℝ → ℝ) (γ : ℝ → PhasePoint) (hγ : IsHamiltonTrajectory H e γ)
    (f : PhasePolynomial) (sParam : ℝ) :
    HasDerivAt (fun t => evalAt f (γ t))
      (evalAt (constrainedRate (e sParam) H f) (γ sParam)) sParam := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    simpa [evalAt, constrainedRate] using (hasDerivAt_const sParam r)
  | add f g hf hg =>
    simpa [evalAt, constrainedRate, poisson_add_left] using hf.add hg
  | mul_X f i hf =>
    simpa [evalAt, constrainedRate, poisson_mul_left] using hf.mul (hγ sParam i)

theorem constraint_hasDerivAt_zero (H : PhasePolynomial) (e : ℝ → ℝ)
    (γ : ℝ → PhasePoint) (hγ : IsHamiltonTrajectory H e γ) (sParam : ℝ) :
    HasDerivAt (fun t => evalAt H (γ t)) 0 sParam := by
  simpa [constraint_rate_zero, evalAt] using
    hasDerivAt_eval_along_hamiltonian H e γ hγ H sParam

/-- Hamilton方程式を満たす全実数上の軌道では、制約の値は実際に一定である。 -/
theorem constraint_constant_along_trajectory (H : PhasePolynomial) (e : ℝ → ℝ)
    (γ : ℝ → PhasePoint) (hγ : IsHamiltonTrajectory H e γ) (s t : ℝ) :
    evalAt H (γ s) = evalAt H (γ t) :=
  is_const_of_deriv_eq_zero
    (fun sParam => (constraint_hasDerivAt_zero H e γ hγ sParam).differentiableAt)
    (fun sParam => (constraint_hasDerivAt_zero H e γ hγ sParam).deriv) s t

def OnMassShell (μ : ℝ) (V : ConfigurationPolynomial) (z : PhasePoint) : Prop :=
  evalAt (massShellPolynomial μ V) z = 0

theorem massShell_preserved (μ : ℝ) (V : ConfigurationPolynomial)
    (e : ℝ → ℝ) (γ : ℝ → PhasePoint)
    (hγ : IsHamiltonTrajectory (massShellPolynomial μ V) e γ)
    (s : ℝ) (hs : OnMassShell μ V (γ s)) (t : ℝ) :
    OnMassShell μ V (γ t) := by
  change evalAt (massShellPolynomial μ V) (γ t) = 0
  rw [constraint_constant_along_trajectory (massShellPolynomial μ V) e γ hγ t s]
  exact hs

/-- 保存条件を満たす任意の多項式も、同じ連鎖律により軌道上で保存される。 -/
theorem observable_constant_of_rate_zero (H f : PhasePolynomial)
    (e : ℝ → ℝ) (γ : ℝ → PhasePoint) (hγ : IsHamiltonTrajectory H e γ)
    (hf : ∀ sParam, constrainedRate (e sParam) H f = 0) (s t : ℝ) :
    evalAt f (γ s) = evalAt f (γ t) := by
  have hd (sParam : ℝ) : HasDerivAt (fun u => evalAt f (γ u)) 0 sParam := by
    simpa [hf sParam, evalAt] using
      hasDerivAt_eval_along_hamiltonian H e γ hγ f sParam
  exact is_const_of_deriv_eq_zero (fun sParam => (hd sParam).differentiableAt)
    (fun sParam => (hd sParam).deriv) s t

theorem temporalMomentum_conserved_of_symmetry (μ : ℝ) (V : ConfigurationPolynomial)
    (e : ℝ → ℝ) (γ : ℝ → PhasePoint)
    (hγ : IsHamiltonTrajectory (massShellPolynomial μ V) e γ)
    (a : TemporalIndex) (hV : MvPolynomial.pderiv (Sum.inr a) V = 0) (s t : ℝ) :
    pValue (γ s) (Sum.inr a) = pValue (γ t) (Sum.inr a) := by
  have hc := observable_constant_of_rate_zero (massShellPolynomial μ V)
    (pPolynomial (Sum.inr a)) e γ hγ
    (fun sParam => momentum_rate_zero_of_translation_invariant (e sParam) μ V (Sum.inr a) hV) s t
  simpa [evalAt, pPolynomial, phaseValues] using hc

/-! ## 2.4　単一制約の第一級閉包と、複数制約との区別 -/

/-- 多項式係数の構造関数による第一級閉包条件。 -/
def FirstClassFamily {ι : Type*} [Fintype ι] (C : ι → PhasePolynomial) : Prop :=
  ∀ a b, ∃ coefficients : ι → PhasePolynomial,
    poissonBracket (C a) (C b) = ∑ j, coefficients j * C j

theorem singleton_firstClass (C : PhasePolynomial) :
    FirstClassFamily (fun _ : Fin 1 => C) := by
  intro a b
  refine ⟨fun _ => 0, ?_⟩
  simp [poisson_self]

/-!
## 証明範囲と依存関係

* canonicalBilinear / omega_alternating / omega_nondegenerate：
  第一章の実12次元空間上の非退化な交代双線形形式。
* canonicalForm_closed / canonicalForm_smooth：
  平坦な相空間における定数係数2形式の閉性と係数関数の滑らかさ。
  外微分の座標式にはFréchet微分を用いる。
* poisson_q_p / poisson_q_q / poisson_p_p / poisson_jacobi：
  実多項式に対する基本括弧とJacobi恒等式。多項式への閉包は型でも保証する。
* omega_hamiltonianVector / poisson_as_hamiltonian_direction：
  2形式、Hamiltonベクトルの成分、形式偏微分の成分式の対応。
* momentum_rate / temporalEnergy_rate：
  質量殻の保存と区別した、相互作用に依存する共役量の変化率。
* hasDerivAt_eval_along_hamiltonian：
  座標ごとのHamilton方程式から、任意の多項式の軌道上の微分を導く連鎖律。
* massShell_preserved / temporalMomentum_conserved_of_symmetry：
  全実数上のHamilton軌道を仮定した、実際の保存則。
  そのような軌道が存在すること自体は、この章では証明していない。
* singleton_firstClass：
  単一制約の多項式係数による第一級閉包。
  任意の複数制約の閉包や、三つの独立時計の整合性は含まない。

位相空間上の正準構造に、時空計量の符号数を入れてはいない。
符号数(3,3)はmassShellPolynomialのkineticPolynomialに明示した。
有限格子への置換・場の量子化・安定性・散乱の保証は、後続章の対象である。
-/

#print axioms omega_nondegenerate
#print axioms canonicalForm_closed
#print axioms poisson_jacobi
#print axioms omega_hamiltonianVector
#print axioms momentum_rate
#print axioms hasDerivAt_eval_along_hamiltonian
#print axioms massShell_preserved
#print axioms temporalMomentum_conserved_of_symmetry
#print axioms linear_time_potential_momentum_rate_ne_zero
#print axioms singleton_firstClass

end Canonical
end TwelveDimensionalPhaseSpace
