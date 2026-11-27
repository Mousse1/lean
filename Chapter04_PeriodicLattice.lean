import Chapter03_Discretization
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# 第四章　周期格子・内部シフト・差分作用素

内部格子G_N=ZMod N×ZMod Nの並進から実際の行列を構成する。
ユニタリ性・周期性・可換性を証明し、第一章のInternalShiftsへ接続する。

次に任意の有限次元ユニタリ行列について、
d†d=K、0≤K≤4/a²、二方向では0≤L≤8/a²を証明する。
不等式は半正定値行列によるLoewner順序として記述する。
離散フーリエ変換や個々の固有値の計算を前提にしない。

## 利用方法

第一〜第三章と同じmathlibプロジェクトで使用する。
先行章のコンパイル済みモジュールがまだない場合：

    lake env lean -o .lake/build/lib/lean/Chapter01_Definitions.olean Chapter01_Definitions.lean
    lake env lean -o .lake/build/lib/lean/Chapter02_CanonicalStructure.olean Chapter02_CanonicalStructure.lean
    lake env lean -o .lake/build/lib/lean/Chapter03_Discretization.olean Chapter03_Discretization.lean
    lake env lean -DwarningAsError=true Chapter04_PeriodicLattice.lean

検証環境：Lean 4.24.0 / mathlib v4.24.0。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
主要定理の公理依存は末尾のコマンドで確認する。
-/

noncomputable section
open scoped BigOperators ComplexOrder

namespace TwelveDimensionalPhaseSpace
namespace Lattice

open Discretization

/-! ## 4.1　巡回並進と内部シフトの構成 -/

def translationPerm {N : ℕ} [NeZero N] (r : Grid N) : Equiv.Perm (Grid N) where
  toFun x := x - r
  invFun x := x + r
  left_inv x := sub_add_cancel x r
  right_inv x := add_sub_cancel_right x r

/--
成分表示は(S_r v)(n)=v(n-r)。
基底状態|n>を|n+r>へ送る向きの並進行列である。
-/
def shiftBy {N : ℕ} [NeZero N] (r : Grid N) : InternalMatrix N :=
  (translationPerm r).toPEquiv.toMatrix

section GridTranslations

variable {N : ℕ} [NeZero N]

@[simp] theorem shiftBy_entry (r i j : Grid N) :
    shiftBy r i j = if j = i - r then 1 else 0 := by
  simp [shiftBy, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    translationPerm, eq_comm]

theorem shiftBy_mulVec (r : Grid N) (v : InternalVector N) :
    (shiftBy r).mulVec v = fun n => v (n - r) := by
  simpa [shiftBy, translationPerm, Function.comp_def] using
    PEquiv.toMatrix_toPEquiv_mulVec (translationPerm r) v

/-- 異なる格子並進は異なる行列になる。自明な表現だけを構成しているのではない。 -/
theorem shiftBy_injective : Function.Injective (shiftBy (N := N)) := by
  intro r s h
  have he := congrArg (fun A : InternalMatrix N => A r 0) h
  by_cases hz : (0 : Grid N) = r - s
  · exact sub_eq_zero.mp hz.symm
  · simp [hz] at he

theorem shiftBy_constant (r : Grid N) (c : ℂ) :
    (shiftBy r).mulVec (fun _ : Grid N => c) = fun _ : Grid N => c := by
  rw [shiftBy_mulVec]

@[simp] theorem shiftBy_zero : shiftBy (0 : Grid N) = 1 := by
  ext i j
  simp [Matrix.one_apply, eq_comm]

theorem shiftBy_add (r s : Grid N) :
    shiftBy r * shiftBy s = shiftBy (r + s) := by
  rw [shiftBy, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [Matrix.submatrix_apply, translationPerm, sub_sub]

theorem shiftBy_adjoint (r : Grid N) :
    (shiftBy r).conjTranspose = shiftBy (-r) := by
  ext i j
  simp [Matrix.conjTranspose_apply, eq_sub_iff_add_eq, eq_comm]

theorem shiftBy_unitary (r : Grid N) : IsUnitaryMatrix (shiftBy r) := by
  constructor
  · rw [shiftBy_adjoint, shiftBy_add, neg_add_cancel, shiftBy_zero]
  · rw [shiftBy_adjoint, shiftBy_add, add_neg_cancel, shiftBy_zero]

theorem shiftBy_commute (r s : Grid N) :
    shiftBy r * shiftBy s = shiftBy s * shiftBy r := by
  rw [shiftBy_add, shiftBy_add, add_comm r s]

theorem shiftBy_pow (r : Grid N) (k : ℕ) :
    (shiftBy r) ^ k = shiftBy (k • r) := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [pow_succ, hk, shiftBy_add]
    rw [add_nsmul, one_nsmul]

omit [NeZero N] in
theorem grid_nsmul_eq_zero (r : Grid N) : N • r = 0 := by
  apply Prod.ext
  · change N • r.1 = 0
    simp [nsmul_eq_mul]
  · change N • r.2 = 0
    simp [nsmul_eq_mul]

theorem shiftBy_periodic (r : Grid N) : (shiftBy r) ^ N = 1 := by
  rw [shiftBy_pow, grid_nsmul_eq_zero, shiftBy_zero]

end GridTranslations

def firstDirection (N : ℕ) : Grid N := (1, 0)
def secondDirection (N : ℕ) : Grid N := (0, 1)

def firstShift (N : ℕ) [NeZero N] : InternalMatrix N :=
  shiftBy (firstDirection N)

def secondShift (N : ℕ) [NeZero N] : InternalMatrix N :=
  shiftBy (secondDirection N)

theorem firstShift_action {N : ℕ} [NeZero N] (v : InternalVector N) (n : Grid N) :
    (firstShift N).mulVec v n = v (n.1 - 1, n.2) := by
  rw [firstShift, shiftBy_mulVec]
  apply congrArg v
  apply Prod.ext
  · rfl
  · exact sub_zero n.2

theorem secondShift_action {N : ℕ} [NeZero N] (v : InternalVector N) (n : Grid N) :
    (secondShift N).mulVec v n = v (n.1, n.2 - 1) := by
  rw [secondShift, shiftBy_mulVec]
  apply congrArg v
  apply Prod.ext
  · exact sub_zero n.1
  · rfl

/-- 第一章では条件として与えた内部シフトを、任意のN≥1で実際に構成する。 -/
def concreteInternalShifts (N : ℕ) [NeZero N] : InternalShifts N where
  first := firstShift N
  second := secondShift N
  first_unitary := shiftBy_unitary (firstDirection N)
  second_unitary := shiftBy_unitary (secondDirection N)
  first_periodic := shiftBy_periodic (firstDirection N)
  second_periodic := shiftBy_periodic (secondDirection N)
  commute := shiftBy_commute (firstDirection N) (secondDirection N)

/-! ## 4.2　一方向の差分因子化と自己共役性 -/

section GeneralUnitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def forwardDifference (a : ℝ) (S : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  a⁻¹ • (S - 1)

theorem unitary_minus_gram (S : Matrix ι ι ℂ) (hS : IsUnitaryMatrix S) :
    (S - 1).conjTranspose * (S - 1) =
      (2 : ℂ) • (1 : Matrix ι ι ℂ) - S - S.conjTranspose := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  calc
    (S.conjTranspose - 1) * (S - 1) =
        S.conjTranspose * S - S.conjTranspose - S + 1 := by noncomm_ring
    _ = (2 : ℂ) • (1 : Matrix ι ι ℂ) - S - S.conjTranspose := by
      rw [hS.1]
      simp only [two_smul]
      abel

theorem unitary_plus_gram (S : Matrix ι ι ℂ) (hS : IsUnitaryMatrix S) :
    (S + 1).conjTranspose * (S + 1) =
      (2 : ℂ) • (1 : Matrix ι ι ℂ) + S + S.conjTranspose := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  calc
    (S.conjTranspose + 1) * (S + 1) =
        S.conjTranspose * S + S.conjTranspose + S + 1 := by noncomm_ring
    _ = (2 : ℂ) • (1 : Matrix ι ι ℂ) + S + S.conjTranspose := by
      rw [hS.1]
      simp only [two_smul]
      abel

theorem difference_factorization (a : ℝ) (S : Matrix ι ι ℂ)
    (hS : IsUnitaryMatrix S) :
    (forwardDifference a S).conjTranspose * forwardDifference a S =
      nearestStencil a S := by
  calc
    (forwardDifference a S).conjTranspose * forwardDifference a S =
        (a⁻¹ * a⁻¹ : ℝ) • ((S - 1).conjTranspose * (S - 1)) := by
      simp [forwardDifference, smul_smul]
    _ = nearestStencil a S := by
      rw [unitary_minus_gram S hS]
      simp [nearestStencil, ← pow_two, inv_pow]

theorem nearestStencil_posSemidef (a : ℝ) (S : Matrix ι ι ℂ)
    (hS : IsUnitaryMatrix S) : (nearestStencil a S).PosSemidef := by
  rw [← difference_factorization a S hS]
  exact Matrix.posSemidef_conjTranspose_mul_self (forwardDifference a S)

theorem nearestStencil_hermitian (a : ℝ) (S : Matrix ι ι ℂ)
    (hS : IsUnitaryMatrix S) : (nearestStencil a S).IsHermitian :=
  (nearestStencil_posSemidef a S hS).isHermitian

/-! ## 4.3　格子サイズによらない一様な上下界 -/

theorem upper_defect_eq_plus_gram (a : ℝ) (S : Matrix ι ι ℂ)
    (hS : IsUnitaryMatrix S) :
    (4 / a ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - nearestStencil a S =
      ((a ^ 2)⁻¹ : ℝ) • ((S + 1).conjTranspose * (S + 1)) := by
  rw [unitary_plus_gram S hS]
  unfold nearestStencil
  have hc : (4 / a ^ 2 : ℝ) =
      (a ^ 2)⁻¹ + (a ^ 2)⁻¹ + (a ^ 2)⁻¹ + (a ^ 2)⁻¹ := by ring
  rw [hc]
  simp only [add_smul, smul_sub, smul_add, two_smul]
  abel

theorem nearestStencil_upper_bound (a : ℝ) (S : Matrix ι ι ℂ)
    (hS : IsUnitaryMatrix S) :
    ((4 / a ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - nearestStencil a S).PosSemidef := by
  rw [upper_defect_eq_plus_gram a S hS]
  exact (Matrix.posSemidef_conjTranspose_mul_self (S + 1)).smul
    (inv_nonneg.mpr (sq_nonneg a))

theorem two_stencil_posSemidef (a : ℝ) (S T : Matrix ι ι ℂ)
    (hS : IsUnitaryMatrix S) (hT : IsUnitaryMatrix T) :
    (nearestStencil a S + nearestStencil a T).PosSemidef :=
  (nearestStencil_posSemidef a S hS).add (nearestStencil_posSemidef a T hT)

theorem two_stencil_upper_bound (a : ℝ) (S T : Matrix ι ι ℂ)
    (hS : IsUnitaryMatrix S) (hT : IsUnitaryMatrix T) :
    ((8 / a ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) -
      (nearestStencil a S + nearestStencil a T)).PosSemidef := by
  have he : (8 / a ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) -
      (nearestStencil a S + nearestStencil a T) =
      ((4 / a ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - nearestStencil a S) +
        ((4 / a ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - nearestStencil a T) := by
    rw [show (8 / a ^ 2 : ℝ) = 4 / a ^ 2 + 4 / a ^ 2 by ring, add_smul]
    abel
  rw [he]
  exact (nearestStencil_upper_bound a S hS).add (nearestStencil_upper_bound a T hT)

end GeneralUnitary

/-! ### 第一章の内部ラプラシアンへの適用 -/

section InternalLaplacianBounds

variable {N : ℕ} [NeZero N]

theorem internalLaplacian_posSemidef (p : ModelParameters) (s : InternalShifts N) :
    (internalLaplacian p s).PosSemidef := by
  rw [internalLaplacian_eq_two_stencils]
  exact two_stencil_posSemidef p.latticeSpacing s.first s.second
    s.first_unitary s.second_unitary

theorem internalLaplacian_hermitian (p : ModelParameters) (s : InternalShifts N) :
    (internalLaplacian p s).IsHermitian :=
  (internalLaplacian_posSemidef p s).isHermitian

/-- (8/a²)I-Lが半正定値、すなわちL≤(8/a²)I。 -/
theorem internalLaplacian_upper_bound (p : ModelParameters) (s : InternalShifts N) :
    (realScalarMatrix (8 / p.latticeSpacing ^ 2) - internalLaplacian p s).PosSemidef := by
  rw [internalLaplacian_eq_two_stencils]
  simpa only [realScalarMatrix, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
    two_stencil_upper_bound p.latticeSpacing s.first s.second
      s.first_unitary s.second_unitary

/-- 実際に構成したN×N周期格子についての上下界をまとめる。 -/
theorem concrete_internalLaplacian_bounds (N : ℕ) [NeZero N] (p : ModelParameters) :
    (internalLaplacian p (concreteInternalShifts N)).PosSemidef ∧
      (realScalarMatrix (8 / p.latticeSpacing ^ 2) -
        internalLaplacian p (concreteInternalShifts N)).PosSemidef :=
  ⟨internalLaplacian_posSemidef p (concreteInternalShifts N),
    internalLaplacian_upper_bound p (concreteInternalShifts N)⟩

/-- 定数場の前進差分はゼロであり、格子の零モードが実際に存在する。 -/
theorem forwardDifference_constant_zero (a : ℝ) (r : Grid N) (c : ℂ) :
    (forwardDifference a (shiftBy r)).mulVec (fun _ : Grid N => c) = 0 := by
  simp [forwardDifference, Matrix.smul_mulVec, Matrix.sub_mulVec, shiftBy_constant]

theorem nearestStencil_constant_zero (a : ℝ) (r : Grid N) (c : ℂ) :
    (nearestStencil a (shiftBy r)).mulVec (fun _ : Grid N => c) = 0 := by
  rw [← difference_factorization a (shiftBy r) (shiftBy_unitary r),
    ← Matrix.mulVec_mulVec, forwardDifference_constant_zero, Matrix.mulVec_zero]

theorem concrete_internalLaplacian_constant_zero (p : ModelParameters) (c : ℂ) :
    (internalLaplacian p (concreteInternalShifts N)).mulVec (fun _ : Grid N => c) = 0 := by
  rw [internalLaplacian_eq_two_stencils, Matrix.add_mulVec]
  change (nearestStencil p.latticeSpacing (shiftBy (firstDirection N))).mulVec
      (fun _ : Grid N => c) +
    (nearestStencil p.latticeSpacing (shiftBy (secondDirection N))).mulVec
      (fun _ : Grid N => c) = 0
  rw [nearestStencil_constant_zero, nearestStencil_constant_zero, zero_add]

/-- 非零の定数ベクトルを伴った、実際の零固有値の存在。 -/
theorem concrete_internalLaplacian_has_zero_mode (p : ModelParameters) :
    ∃ v : InternalVector N, v ≠ 0 ∧
      (internalLaplacian p (concreteInternalShifts N)).mulVec v = 0 := by
  refine ⟨fun _ => 1, ?_, concrete_internalLaplacian_constant_zero p 1⟩
  intro h
  have h0 := congrFun h (0 : Grid N)
  norm_num at h0

end InternalLaplacianBounds

/-!
## 証明した範囲

* shiftBy_entry / shiftBy_mulVec / firstShift_action / secondShift_action：
  巡回格子上の具体的な一格子移動と行列成分の対応。
* shiftBy_injective：
  格子並進の表現が忠実であること。
* shiftBy_unitary / shiftBy_periodic / shiftBy_commute：
  ユニタリ性、N回の周期性、二方向の可換性。
* concreteInternalShifts：
  第一章で条件として与えたデータの、任意N≥1での実際の構成。
* difference_factorization：
  前進差分のGram行列が最近接内部作用素に一致すること。
* nearestStencil_posSemidef / nearestStencil_upper_bound：
  一方向の0≤K≤(4/a²)I。
* internalLaplacian_posSemidef / internalLaplacian_hermitian /
  internalLaplacian_upper_bound / concrete_internalLaplacian_bounds：
  二方向の0≤L≤(8/a²)Iと自己共役性。格子サイズによらない評価。
* concrete_internalLaplacian_has_zero_mode：
  非零の定数ベクトルが零モードを与えること。

一般の行列に対する上下界の補題では、周期性や二方向の可換性を必要とせず、
ユニタリ性から直接評価する。模型への適用では正の格子間隔を使う。
本章で保証するLの半正定値性と、次章で扱うM²の正の下界は別の条件である。
場の時間発展の安定性や散乱保存則は、後続章で証明する。
-/

#print axioms shiftBy_injective
#print axioms shiftBy_unitary
#print axioms shiftBy_periodic
#print axioms concreteInternalShifts
#print axioms difference_factorization
#print axioms nearestStencil_posSemidef
#print axioms nearestStencil_upper_bound
#print axioms internalLaplacian_hermitian
#print axioms concrete_internalLaplacian_bounds
#print axioms concrete_internalLaplacian_has_zero_mode

end Lattice
end TwelveDimensionalPhaseSpace
