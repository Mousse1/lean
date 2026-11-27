import Chapter02_CanonicalStructure
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# 第三章　有限化規則と連続模型との対応

有限周期内部状態・最近接差分・標準的な線形スカラー場の方程式を、
模型化の選択として明示する。連続12次元粒子模型からこれらの選択が
一意に導かれるとは主張しない。

本章では、格子の厳密な分散関係、連続二次式との違い、
有限次元正準交換関係のトレース障害を証明する。
連続極限の作用素収束、量子化の一意性、独立時計の実在は含めない。

## 利用方法と検証記録

第一・第二章と同じmathlibプロジェクトで使用する。
先行章のコンパイル済みモジュールがまだない場合のコマンド例：

    lake env lean -o .lake/build/lib/lean/Chapter01_Definitions.olean Chapter01_Definitions.lean
    lake env lean -o .lake/build/lib/lean/Chapter02_CanonicalStructure.olean Chapter02_CanonicalStructure.lean
    lake env lean -DwarningAsError=true Chapter03_Discretization.lean

検証環境はLean 4.24.0 / mathlib v4.24.0。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
警告をエラーとして扱うコンパイルを行う。
主要定理の公理依存は、末尾のコマンドで確認する。
-/

noncomputable section
open scoped BigOperators ComplexOrder

namespace TwelveDimensionalPhaseSpace
namespace Discretization

/-! ## 3.1　採用する有限化と場の方程式 -/

structure FiniteModelData (N : ℕ) [NeZero N] where
  parameters : ModelParameters
  shifts : InternalShifts N
  potential : Potential N

/--
採用する場の方程式の残差：∂τ²Φ-ΔΦ+M²Φ。
derivは全関数に定義されるので、解の正則性は後続章で別に要求する。
この定義だけで、粒子模型からの量子化や解の存在を証明したことにはならない。
-/
def adoptedFieldResidual {N : ℕ} [NeZero N] (D : FiniteModelData N)
    (Φ : CoordinateField N) (τ : ObservedTime) (x : SpatialPosition)
    (i : Grid N) : ℂ :=
  deriv (deriv (fun t : ℝ => Φ t x i)) τ -
    (∑ j : SpatialIndex,
      deriv (deriv (fun r : ℝ => Φ τ (Function.update x j r) i)) (x j)) +
    (massSquared D.parameters D.shifts D.potential τ x).mulVec (Φ τ x) i

def AdoptedFieldEquation {N : ℕ} [NeZero N] (D : FiniteModelData N)
    (Φ : CoordinateField N) : Prop :=
  ∀ τ x i, adoptedFieldResidual D Φ τ x i = 0

section FiniteMatrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- 最近接差分の一方向の寄与。格子間隔の正値性は適用時に要求する。 -/
def nearestStencil (a : ℝ) (S : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (a ^ 2)⁻¹ • ((2 : ℂ) • (1 : Matrix ι ι ℂ) - S - S.conjTranspose)

end FiniteMatrices

theorem internalLaplacian_eq_two_stencils {N : ℕ} [NeZero N]
    (p : ModelParameters) (s : InternalShifts N) :
    internalLaplacian p s =
      nearestStencil p.latticeSpacing s.first +
        nearestStencil p.latticeSpacing s.second := by
  simp [internalLaplacian, nearestStencil, smul_add]

/-! ## 3.2　有限格子の分散関係 -/

/-- 単位円上の位相。後で複素指数関数との一致も示す。 -/
def phase (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I

theorem phase_eq_exp (θ : ℝ) :
    phase θ = Complex.exp ((θ : ℂ) * Complex.I) := by
  simp [phase, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem phase_star_mul (θ : ℝ) : star (phase θ) * phase θ = 1 := by
  rw [phase_eq_exp]
  change (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) *
    Complex.exp ((θ : ℂ) * Complex.I) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem phase_mul_star (θ : ℝ) : phase θ * star (phase θ) = 1 := by
  rw [mul_comm, phase_star_mul]

@[simp] theorem phase_conj_mul (θ : ℝ) :
    (starRingEnd ℂ) (phase θ) * phase θ = 1 :=
  phase_star_mul θ

@[simp] theorem phase_mul_conj (θ : ℝ) :
    phase θ * (starRingEnd ℂ) (phase θ) = 1 :=
  phase_mul_star θ

theorem phase_star (θ : ℝ) : star (phase θ) = phase (-θ) := by
  apply Complex.ext <;> simp [phase]

theorem phase_periodic : Function.Periodic phase (2 * Real.pi) := by
  intro θ
  simp [phase, Real.cos_add, Real.sin_add]

theorem phase_stencil (θ : ℝ) :
    (2 : ℂ) - phase θ - star (phase θ) = (2 - 2 * Real.cos θ : ℝ) := by
  apply Complex.ext <;> simp [phase]
  ring

/-- Kの実固有値。連続模型のκ²とは区別する。 -/
def latticeSymbol (a κ : ℝ) : ℝ :=
  (2 - 2 * Real.cos (a * κ)) / a ^ 2

theorem latticeSymbol_sine (a κ : ℝ) :
    latticeSymbol a κ = (4 / a ^ 2) * Real.sin (a * κ / 2) ^ 2 := by
  rw [Real.sin_sq_eq_half_sub]
  rw [show 2 * (a * κ / 2) = a * κ by ring]
  unfold latticeSymbol
  ring

theorem scalarStencil_symbol (a κ : ℝ) :
    ((a ^ 2)⁻¹ : ℝ) •
      ((2 : ℂ) - phase (a * κ) - star (phase (a * κ))) =
        (latticeSymbol a κ : ℂ) := by
  rw [phase_stencil, Complex.real_smul]
  simp only [latticeSymbol, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow,
    Complex.ofReal_inv]
  ring

@[simp] theorem latticeSymbol_zero (a : ℝ) : latticeSymbol a 0 = 0 := by
  simp [latticeSymbol]

theorem latticeSymbol_nonneg (a κ : ℝ) : 0 ≤ latticeSymbol a κ := by
  rw [latticeSymbol_sine]
  exact mul_nonneg (div_nonneg (by norm_num) (sq_nonneg a)) (sq_nonneg _)

theorem latticeSymbol_le_cutoff (a κ : ℝ) :
    latticeSymbol a κ ≤ 4 / a ^ 2 := by
  rw [latticeSymbol_sine]
  exact mul_le_of_le_one_right (div_nonneg (by norm_num) (sq_nonneg a))
    (Real.sin_sq_le_one _)

theorem latticeSymbol_even (a κ : ℝ) : latticeSymbol a (-κ) = latticeSymbol a κ := by
  simp [latticeSymbol]

theorem latticeSymbol_periodic (a : ℝ) (ha : a ≠ 0) :
    Function.Periodic (latticeSymbol a) (2 * Real.pi / a) := by
  intro κ
  unfold latticeSymbol
  rw [show a * (κ + 2 * Real.pi / a) = a * κ + 2 * Real.pi by
    field_simp]
  simp

/-- 有限aの非零波数では、最近接の格子寄与は連続二次式より厳密に小さい。 -/
theorem latticeSymbol_lt_quadratic (a κ : ℝ) (ha : a ≠ 0) (hκ : κ ≠ 0) :
    latticeSymbol a κ < κ ^ 2 := by
  have hx : a * κ / 2 ≠ 0 := div_ne_zero (mul_ne_zero ha hκ) (by norm_num)
  have hp : 0 < 4 / a ^ 2 := div_pos (by norm_num) (sq_pos_of_ne_zero ha)
  have hs := mul_lt_mul_of_pos_left (Real.sin_sq_lt_sq hx) hp
  rw [← latticeSymbol_sine] at hs
  have hc : (4 / a ^ 2) * (a * κ / 2) ^ 2 = κ ^ 2 := by
    field_simp
    ring
  rwa [hc] at hs

theorem latticeSymbol_le_quadratic (a κ : ℝ) (ha : a ≠ 0) :
    latticeSymbol a κ ≤ κ ^ 2 := by
  by_cases hκ : κ = 0
  · subst κ
    simp
  · exact (latticeSymbol_lt_quadratic a κ ha hκ).le

/-- 二方向の格子寄与も、少なくとも一方向が非零なら連続二次式と一致しない。 -/
theorem two_axis_symbol_lt_quadratic (a κ₁ κ₂ : ℝ) (ha : a ≠ 0)
    (hκ : κ₁ ≠ 0 ∨ κ₂ ≠ 0) :
    latticeSymbol a κ₁ + latticeSymbol a κ₂ < κ₁ ^ 2 + κ₂ ^ 2 := by
  rcases hκ with h₁ | h₂
  · exact add_lt_add_of_lt_of_le (latticeSymbol_lt_quadratic a κ₁ ha h₁)
      (latticeSymbol_le_quadratic a κ₂ ha)
  · exact add_lt_add_of_le_of_lt (latticeSymbol_le_quadratic a κ₁ ha)
      (latticeSymbol_lt_quadratic a κ₂ ha h₂)

/-- 連続模型と有限格子模型で比較する、自由分散関係の左辺。 -/
def continuumDispersionResidual (μ ω : ℝ) (p : SpatialMomenta) (κ₁ κ₂ : ℝ) : ℝ :=
  ω ^ 2 - (∑ i, p i ^ 2) - μ ^ 2 + κ₁ ^ 2 + κ₂ ^ 2

def latticeDispersionResidual (a μ ω : ℝ) (p : SpatialMomenta) (κ₁ κ₂ : ℝ) : ℝ :=
  ω ^ 2 - (∑ i, p i ^ 2) - μ ^ 2 + latticeSymbol a κ₁ + latticeSymbol a κ₂

theorem dispersion_residual_difference (a μ ω : ℝ) (p : SpatialMomenta) (κ₁ κ₂ : ℝ) :
    latticeDispersionResidual a μ ω p κ₁ κ₂ - continuumDispersionResidual μ ω p κ₁ κ₂ =
      (latticeSymbol a κ₁ + latticeSymbol a κ₂) - (κ₁ ^ 2 + κ₂ ^ 2) := by
  unfold latticeDispersionResidual continuumDispersionResidual
  ring

/-- 同じμ,ω,p,κを固定すると、非零内部波数で二つの質量殻は一致しない。 -/
theorem continuum_shell_not_lattice_shell (a μ ω : ℝ) (p : SpatialMomenta)
    (κ₁ κ₂ : ℝ) (ha : a ≠ 0) (hκ : κ₁ ≠ 0 ∨ κ₂ ≠ 0)
    (hc : continuumDispersionResidual μ ω p κ₁ κ₂ = 0) :
    latticeDispersionResidual a μ ω p κ₁ κ₂ < 0 := by
  have hs := two_axis_symbol_lt_quadratic a κ₁ κ₂ ha hκ
  have hd := dispersion_residual_difference a μ ω p κ₁ κ₂
  linarith

/-!
### 指定したスペクトル表示における厳密な行列恒等式

実固有値κとユニタリ基底Uを与え、Π=U diag(κ) U†と
S=U diag(exp(i a κ)) U†を構成する。半角のsinも同じ基底による
有限次元関数計算で構成し、K=(4/a²)sin²(aΠ/2)を証明する。

ここで一般のSの対数の存在を仮定・証明してはいない。
また、一般のκから作ったSがS^N=Iを満たすとは主張しない。
周期格子には、さらに許容する固有位相を選ぶ条件が必要である。
-/

section SpectralRepresentation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def conjugateBy (U A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  U * A * U.conjTranspose

theorem conjugateBy_one (U : Matrix ι ι ℂ) (hU : IsUnitaryMatrix U) :
    conjugateBy U 1 = 1 := by
  simpa [conjugateBy] using hU.2

omit [DecidableEq ι] in
theorem conjugateBy_sub (U A B : Matrix ι ι ℂ) :
    conjugateBy U (A - B) = conjugateBy U A - conjugateBy U B := by
  simp [conjugateBy, Matrix.mul_sub, Matrix.sub_mul]

theorem conjugateBy_smul_real (U A : Matrix ι ι ℂ) (r : ℝ) :
    conjugateBy U (r • A) = r • conjugateBy U A := by
  simp [conjugateBy]

theorem conjugateBy_smul_complex (U A : Matrix ι ι ℂ) (c : ℂ) :
    conjugateBy U (c • A) = c • conjugateBy U A := by
  simp [conjugateBy]

omit [DecidableEq ι] in
theorem conjugateBy_adjoint (U A : Matrix ι ι ℂ) :
    (conjugateBy U A).conjTranspose = conjugateBy U A.conjTranspose := by
  simp [conjugateBy, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem conjugateBy_mul (U A B : Matrix ι ι ℂ) (hU : IsUnitaryMatrix U) :
    conjugateBy U A * conjugateBy U B = conjugateBy U (A * B) := by
  unfold conjugateBy
  calc
    (U * A * U.conjTranspose) * (U * B * U.conjTranspose) =
        U * A * (U.conjTranspose * U) * B * U.conjTranspose := by noncomm_ring
    _ = U * (A * B) * U.conjTranspose := by
      rw [hU.1]
      simp [Matrix.mul_assoc]

theorem conjugateBy_cancel (U A : Matrix ι ι ℂ) (hU : IsUnitaryMatrix U) :
    conjugateBy U.conjTranspose (conjugateBy U A) = A := by
  unfold conjugateBy
  rw [Matrix.conjTranspose_conjTranspose]
  calc
    U.conjTranspose * (U * A * U.conjTranspose) * U =
        (U.conjTranspose * U) * A * (U.conjTranspose * U) := by noncomm_ring
    _ = A := by simp [hU.1]

theorem conjugateBy_injective (U : Matrix ι ι ℂ) (hU : IsUnitaryMatrix U) :
    Function.Injective (conjugateBy U) := by
  intro A B h
  have hc := congrArg (conjugateBy U.conjTranspose) h
  simpa only [conjugateBy_cancel U A hU, conjugateBy_cancel U B hU] using hc

theorem conjugateBy_unitary (U A : Matrix ι ι ℂ)
    (hU : IsUnitaryMatrix U) (hA : IsUnitaryMatrix A) :
    IsUnitaryMatrix (conjugateBy U A) := by
  constructor
  · rw [conjugateBy_adjoint, conjugateBy_mul U A.conjTranspose A hU,
      hA.1, conjugateBy_one U hU]
  · rw [conjugateBy_adjoint, conjugateBy_mul U A A.conjTranspose hU,
      hA.2, conjugateBy_one U hU]

def diagonalReal (r : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => (r i : ℂ))

def diagonalPhase (a : ℝ) (κ : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => phase (a * κ i))

omit [Fintype ι] in
theorem diagonalReal_adjoint (r : ι → ℝ) :
    (diagonalReal r).conjTranspose = diagonalReal r := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [diagonalReal, Matrix.conjTranspose_apply]
  · simp [diagonalReal, Matrix.conjTranspose_apply, h, Ne.symm h]

theorem diagonalPhase_unitary (a : ℝ) (κ : ι → ℝ) :
    IsUnitaryMatrix (diagonalPhase a κ) := by
  simp [IsUnitaryMatrix, diagonalPhase, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]

def spectralGenerator (U : Matrix ι ι ℂ) (κ : ι → ℝ) : Matrix ι ι ℂ :=
  conjugateBy U (diagonalReal κ)

def spectralShift (U : Matrix ι ι ℂ) (a : ℝ) (κ : ι → ℝ) : Matrix ι ι ℂ :=
  conjugateBy U (diagonalPhase a κ)

def spectralHalfSine (U : Matrix ι ι ℂ) (a : ℝ) (κ : ι → ℝ) : Matrix ι ι ℂ :=
  conjugateBy U (diagonalReal (fun i => Real.sin (a * κ i / 2)))

theorem spectralGenerator_hermitian (U : Matrix ι ι ℂ) (κ : ι → ℝ) :
    (spectralGenerator U κ).IsHermitian := by
  change (conjugateBy U (diagonalReal κ)).conjTranspose = conjugateBy U (diagonalReal κ)
  rw [conjugateBy_adjoint, diagonalReal_adjoint]

theorem spectralShift_unitary (U : Matrix ι ι ℂ) (a : ℝ) (κ : ι → ℝ)
    (hU : IsUnitaryMatrix U) : IsUnitaryMatrix (spectralShift U a κ) :=
  conjugateBy_unitary U (diagonalPhase a κ) hU (diagonalPhase_unitary a κ)

omit [Fintype ι] in
theorem nearestStencil_diagonalPhase (a : ℝ) (κ : ι → ℝ) :
    nearestStencil a (diagonalPhase a κ) =
      diagonalReal (fun i => latticeSymbol a (κ i)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simpa [nearestStencil, diagonalPhase, diagonalReal,
      Matrix.conjTranspose_apply] using scalarStencil_symbol a (κ i)
  · simp [nearestStencil, diagonalPhase, diagonalReal, h]

theorem nearestStencil_conjugateBy (U A : Matrix ι ι ℂ) (a : ℝ)
    (hU : IsUnitaryMatrix U) :
    nearestStencil a (conjugateBy U A) = conjugateBy U (nearestStencil a A) := by
  simp only [nearestStencil, conjugateBy_smul_real, conjugateBy_sub,
    conjugateBy_smul_complex, conjugateBy_one U hU, ← conjugateBy_adjoint]

theorem spectral_stencil_symbol (U : Matrix ι ι ℂ) (a : ℝ) (κ : ι → ℝ)
    (hU : IsUnitaryMatrix U) :
    nearestStencil a (spectralShift U a κ) =
      conjugateBy U (diagonalReal (fun i => latticeSymbol a (κ i))) := by
  rw [spectralShift, nearestStencil_conjugateBy U (diagonalPhase a κ) a hU,
    nearestStencil_diagonalPhase]

theorem diagonalSymbol_sine (a : ℝ) (κ : ι → ℝ) :
    diagonalReal (fun i => latticeSymbol a (κ i)) =
      (4 / a ^ 2 : ℝ) •
        (diagonalReal (fun i => Real.sin (a * κ i / 2)) *
          diagonalReal (fun i => Real.sin (a * κ i / 2))) := by
  have hs (i : ι) : (latticeSymbol a (κ i) : ℂ) =
      (4 / a ^ 2 : ℝ) • ((Real.sin (a * κ i / 2) : ℂ) ^ 2) := by
    rw [Complex.real_smul, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    exact congrArg (fun r : ℝ => (r : ℂ)) (latticeSymbol_sine a (κ i))
  simp only [diagonalReal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simpa [pow_two] using hs i
  · simp [h]

/-- 指定したスペクトル表示における、有限aで厳密な行列のsin²関係。 -/
theorem spectral_stencil_sine (U : Matrix ι ι ℂ) (a : ℝ) (κ : ι → ℝ)
    (hU : IsUnitaryMatrix U) :
    nearestStencil a (spectralShift U a κ) =
      (4 / a ^ 2 : ℝ) • (spectralHalfSine U a κ) ^ 2 := by
  rw [spectral_stencil_symbol U a κ hU, diagonalSymbol_sine, conjugateBy_smul_real]
  simp only [spectralHalfSine, pow_two, conjugateBy_mul U _ _ hU]

theorem spectralGenerator_square (U : Matrix ι ι ℂ) (κ : ι → ℝ)
    (hU : IsUnitaryMatrix U) :
    (spectralGenerator U κ) ^ 2 =
      conjugateBy U (diagonalReal (fun i => κ i ^ 2)) := by
  rw [spectralGenerator, pow_two, conjugateBy_mul U _ _ hU]
  apply congrArg (conjugateBy U)
  simp [diagonalReal, pow_two]

/-- 非零固有値があれば、有限aで格子寄与Kと生成子の二乗Π²は行列としても異なる。 -/
theorem spectral_stencil_ne_generator_square (U : Matrix ι ι ℂ)
    (a : ℝ) (κ : ι → ℝ) (hU : IsUnitaryMatrix U)
    (ha : a ≠ 0) (hκ : ∃ i, κ i ≠ 0) :
    nearestStencil a (spectralShift U a κ) ≠ (spectralGenerator U κ) ^ 2 := by
  intro h
  rw [spectral_stencil_symbol U a κ hU, spectralGenerator_square U κ hU] at h
  have hd := conjugateBy_injective U hU h
  obtain ⟨i, hi⟩ := hκ
  have he : latticeSymbol a (κ i) = κ i ^ 2 := by
    apply Complex.ofReal_injective
    simpa [diagonalReal] using congrArg (fun A : Matrix ι ι ℂ => A i i) hd
  exact (ne_of_lt (latticeSymbol_lt_quadratic a (κ i) ha hi)) he

end SpectralRepresentation

/-!
周期性・反転対称性・零モード・非負性だけでは最近接の具体形は決まらない。
次の修正は最近接という条件を緩めた例であり、同じ最近接作用ではない。
長波長漸近展開や作用素の連続極限については、この例から結論しない。
-/

def modifiedSymbol (a κ : ℝ) : ℝ :=
  latticeSymbol a κ + a ^ 2 * latticeSymbol a κ ^ 2

@[simp] theorem modifiedSymbol_zero (a : ℝ) : modifiedSymbol a 0 = 0 := by
  simp [modifiedSymbol]

theorem modifiedSymbol_nonneg (a κ : ℝ) : 0 ≤ modifiedSymbol a κ :=
  add_nonneg (latticeSymbol_nonneg a κ) (mul_nonneg (sq_nonneg a) (sq_nonneg _))

theorem modifiedSymbol_even (a κ : ℝ) : modifiedSymbol a (-κ) = modifiedSymbol a κ := by
  simp [modifiedSymbol, latticeSymbol_even]

theorem modifiedSymbol_periodic (a : ℝ) (ha : a ≠ 0) :
    Function.Periodic (modifiedSymbol a) (2 * Real.pi / a) := by
  intro κ
  simp only [modifiedSymbol, latticeSymbol_periodic a ha κ]

theorem modifiedSymbol_differs :
    modifiedSymbol 1 Real.pi ≠ latticeSymbol 1 Real.pi := by
  norm_num [modifiedSymbol, latticeSymbol]

/-! ## 3.3　有限次元の正準交換関係の障害 -/

section TraceObstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem commutator_trace (X P : Matrix ι ι ℂ) :
    Matrix.trace (X * P - P * X) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm X P, sub_self]

/--
正の有限次元では、交換子は非零の定数倍の単位行列にはならない。
X,Pの自己共役性さえ必要としない。
-/
theorem no_nonzero_scalar_commutator [Nonempty ι]
    (X P : Matrix ι ι ℂ) (c : ℂ) (hc : c ≠ 0) :
    X * P - P * X ≠ c • (1 : Matrix ι ι ℂ) := by
  intro h
  have ht := congrArg Matrix.trace h
  rw [commutator_trace, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at ht
  have hn : (Fintype.card ι : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos)
  exact (mul_ne_zero hc hn) ht.symm

theorem no_finite_CCR [Nonempty ι] (X P : Matrix ι ι ℂ) (ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    X * P - P * X ≠ ((ℏ : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) :=
  no_nonzero_scalar_commutator X P _ (mul_ne_zero (Complex.ofReal_ne_zero.mpr hℏ)
    Complex.I_ne_zero)

end TraceObstruction

theorem no_internal_grid_CCR {N : ℕ} [NeZero N]
    (X P : InternalMatrix N) :
    X * P - P * X ≠ Complex.I • (1 : InternalMatrix N) := by
  simpa using no_finite_CCR X P 1 (by norm_num)

/-!
## 証明した範囲

1. FiniteModelData / AdoptedFieldEquation：
   最近接差分と線形スカラー場の方程式を採用する定義。
   連続粒子模型からの一意な導出を意味しない。
2. latticeSymbol_sine / scalarStencil_symbol：
   有限の格子間隔で厳密に成立するスカラー分散関係。
3. spectralGenerator_hermitian / spectralShift_unitary / spectral_stencil_sine：
   指定したユニタリ基底Uと実固有値κから構成した自己共役生成子、
   ユニタリ演算子と最近接差分作用素の厳密な行列関係。
   半角sinはspectralHalfSineとして同じスペクトル表示で定義している。
   任意のユニタリ行列について対数を構成する定理や、
   mathlibの一般の行列指数関数との相互運用は本章に含めない。
4. latticeSymbol_lt_quadratic / spectral_stencil_ne_generator_square：
   a≠0で非零の内部波数・生成子固有値を持つ場合の、
   連続二次式と格子寄与の厳密な相違。
5. continuum_shell_not_lattice_shell：
   同じμ,ω,p,κを保つ場合に、二つの自由質量殻が一般には一致しないこと。
   変数の再定義を許した模型全体の非同値性を述べる定理ではない。
6. modifiedSymbol_differsとその前の性質：
   周期性・反転対称性・零モード・非負性だけでは、
   最近接の具体的な分散関係を一意に選べないことの例。
7. no_finite_CCR / no_internal_grid_CCR：
   正の有限次元では[X,P]=iℏIをℏ≠0で実現できないこと。
   この定理は有限Weyl関係を禁止するものではない。

残る課題：

具体的な巡回置換からの内部シフトの構成は第四章、
行列の正値性と安定性の条件は第五章以降で扱う。
連続極限の収束、量子化の対応、独立時計との結合は別の研究課題である。
-/

#print axioms latticeSymbol_sine
#print axioms latticeSymbol_lt_quadratic
#print axioms continuum_shell_not_lattice_shell
#print axioms spectralGenerator_hermitian
#print axioms spectralShift_unitary
#print axioms spectral_stencil_sine
#print axioms spectral_stencil_ne_generator_square
#print axioms modifiedSymbol_differs
#print axioms no_finite_CCR
#print axioms no_internal_grid_CCR

end Discretization
end TwelveDimensionalPhaseSpace
