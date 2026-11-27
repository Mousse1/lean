import Chapter04_PeriodicLattice

set_option autoImplicit false

/-!
# 第五章　質量行列の自己共役性・正値性・具体例

第四章の 0 ≤ L ≤ (8/a²)I から、第一章で定義した質量二乗行列

    M₀² = μ²I - L,    M²(τ,x) = μ²I - L + V(τ,x)

の自己共役性と正の下界を導く。M²という名前から正値性を仮定しない。

中心となる結論は、V(τ,x) ≥ vMin I ならば

    M²(τ,x) ≥ δ I,    δ = μ² + vMin - 8/a²

となること。δ > 0 は正定値性の十分条件であり、必要条件とは主張しない。
この行列評価にはVの静的条件や有界性を必要としない。
場のエネルギー保存には別途静的条件などが必要であり、後続章で扱う。

## 利用方法と検証環境

第一〜第四章と同じmathlibプロジェクトで使用する。
先行章を .lake/build/lib/lean にコンパイルした後：

    lake env lean -DwarningAsError=true Chapter05_MassMatrix.lean

検証環境：Lean 4.24.0 / mathlib v4.24.0。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
末尾の #print axioms により主要定理の公理依存を確認する。
-/

noncomputable section
open scoped BigOperators ComplexOrder

namespace TwelveDimensionalPhaseSpace
namespace MassMatrix

variable {N : ℕ}

/-! ## 5.1　実スカラー行列と自己共役性 -/

@[simp]
theorem scalarMatrix_zero : realScalarMatrix (N := N) 0 = 0 := by
  simp [realScalarMatrix]

theorem scalarMatrix_add (r s : ℝ) :
    realScalarMatrix (N := N) (r + s) =
      realScalarMatrix r + realScalarMatrix s := by
  simp [realScalarMatrix, add_smul]

theorem scalarMatrix_sub (r s : ℝ) :
    realScalarMatrix (N := N) (r - s) =
      realScalarMatrix r - realScalarMatrix s := by
  simp [realScalarMatrix, sub_smul]

theorem scalarMatrix_hermitian (r : ℝ) :
    (realScalarMatrix (N := N) r).IsHermitian := by
  change (realScalarMatrix (N := N) r).conjTranspose = realScalarMatrix r
  simp [realScalarMatrix]

variable [NeZero N]

theorem scalarMatrix_posSemidef {r : ℝ} (hr : 0 ≤ r) :
    (realScalarMatrix (N := N) r).PosSemidef := by
  simpa only [realScalarMatrix, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
    (Matrix.PosSemidef.one : (1 : InternalMatrix N).PosSemidef).smul hr

theorem scalarMatrix_posDef {r : ℝ} (hr : 0 < r) :
    (realScalarMatrix (N := N) r).PosDef := by
  simpa only [realScalarMatrix, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
    (Matrix.PosDef.one : (1 : InternalMatrix N).PosDef).smul hr

theorem freeMassSquared_hermitian (p : ModelParameters) (s : InternalShifts N) :
    (freeMassSquared p s).IsHermitian :=
  (scalarMatrix_hermitian (p.massParameter ^ 2)).sub
    (Lattice.internalLaplacian_hermitian p s)

/-- 相互作用の自己共役性から、質量二乗行列全体の自己共役性を導く。 -/
theorem massSquared_hermitian (p : ModelParameters) (s : InternalShifts N)
    (V : Potential N) (hV : IsHermitianPotential V)
    (τ : ObservedTime) (x : SpatialPosition) :
    (massSquared p s V τ x).IsHermitian :=
  (freeMassSquared_hermitian p s).add (hV τ x)

/-! ## 5.2　下界と正定値性 -/

/-- 質量行列の下界を、二つの半正定値行列の和に分解する恒等式。 -/
theorem massGap_decomposition (p : ModelParameters) (s : InternalShifts N)
    (V : Potential N) (τ : ObservedTime) (x : SpatialPosition) :
    massSquared p s V τ x - realScalarMatrix (sufficientMassGap p) =
      (realScalarMatrix (8 / p.latticeSpacing ^ 2) - internalLaplacian p s) +
        (V τ x - realScalarMatrix p.vMin) := by
  rw [sufficientMassGap, scalarMatrix_sub, scalarMatrix_add]
  unfold massSquared freeMassSquared
  abel

/-- 主定理：V ≥ vMin I と L ≤ (8/a²)I から M² ≥ δ I。 -/
theorem massSquared_lower_bound (p : ModelParameters) (s : InternalShifts N)
    (V : Potential N) (hV : HasUniformPotentialLowerBound V p.vMin)
    (τ : ObservedTime) (x : SpatialPosition) :
    HasMatrixLowerBound (massSquared p s V τ x) (sufficientMassGap p) := by
  unfold HasMatrixLowerBound
  rw [massGap_decomposition]
  exact (Lattice.internalLaplacian_upper_bound p s).add (hV τ x)

/-- 下界が与えられた行列の自己共役性。追加の自己共役性仮定は不要。 -/
theorem hermitian_of_lower_bound {A : InternalMatrix N} {r : ℝ}
    (hA : HasMatrixLowerBound A r) : A.IsHermitian := by
  have h := (scalarMatrix_hermitian (N := N) r).add hA.isHermitian
  simpa only [add_sub_cancel] using h

theorem posSemidef_of_lower_bound {A : InternalMatrix N} {r : ℝ}
    (hA : HasMatrixLowerBound A r) (hr : 0 ≤ r) : A.PosSemidef := by
  have h := (scalarMatrix_posSemidef (N := N) hr).add hA
  simpa only [add_sub_cancel] using h

/-- 厳密に正の下界を持つ行列は正定値。結論自体を仮定に含めない。 -/
theorem posDef_of_lower_bound {A : InternalMatrix N} {r : ℝ}
    (hA : HasMatrixLowerBound A r) (hr : 0 < r) : A.PosDef := by
  have h := (scalarMatrix_posDef (N := N) hr).add_posSemidef hA
  simpa only [add_sub_cancel] using h

theorem massSquared_posSemidef (p : ModelParameters) (s : InternalShifts N)
    (V : Potential N) (hV : HasUniformPotentialLowerBound V p.vMin)
    (hgap : 0 ≤ sufficientMassGap p) (τ : ObservedTime) (x : SpatialPosition) :
    (massSquared p s V τ x).PosSemidef :=
  posSemidef_of_lower_bound (massSquared_lower_bound p s V hV τ x) hgap

theorem massSquared_posDef (p : ModelParameters) (s : InternalShifts N)
    (V : Potential N) (hV : HasUniformPotentialLowerBound V p.vMin)
    (hgap : PositiveGapCondition p) (τ : ObservedTime) (x : SpatialPosition) :
    (massSquared p s V τ x).PosDef :=
  posDef_of_lower_bound (massSquared_lower_bound p s V hV τ x) hgap

/-- 第一章の仮定集から、実際に正定値性が導かれることを接続する。 -/
theorem massSquared_posDef_of_stabilityHypotheses
    (p : ModelParameters) (s : InternalShifts N) (V : Potential N)
    (h : StabilityHypotheses p V) (τ : ObservedTime) (x : SpatialPosition) :
    (massSquared p s V τ x).PosDef :=
  massSquared_posDef p s V h.lowerBound h.positiveGap τ x

/-- 自由質量二乗は μ²I 以下。下界の証明とは別に L ≥ 0 を使う。 -/
theorem freeMassSquared_upper_bound (p : ModelParameters) (s : InternalShifts N) :
    (realScalarMatrix (p.massParameter ^ 2) - freeMassSquared p s).PosSemidef := by
  simpa only [freeMassSquared, sub_sub_cancel] using
    Lattice.internalLaplacian_posSemidef p s

/-! ## 5.3　参照設定と、実際に存在する模型 -/

theorem nonnegativePotential_lower_bound (V : Potential N)
    (hV : ∀ τ x, (V τ x).PosSemidef) :
    HasUniformPotentialLowerBound V 0 := by
  intro τ x
  simpa only [HasMatrixLowerBound, scalarMatrix_zero, sub_zero] using hV τ x

/-- a=3、μ=1、V ≥ 0 ならば、任意N≥1で M² ≥ (1/9)I。 -/
theorem reference_mass_lower_bound (s : InternalShifts N) (V : Potential N)
    (hV : ∀ τ x, (V τ x).PosSemidef)
    (τ : ObservedTime) (x : SpatialPosition) :
    HasMatrixLowerBound (massSquared referenceParameters s V τ x) (1 / 9) := by
  have hLower : HasUniformPotentialLowerBound V referenceParameters.vMin :=
    nonnegativePotential_lower_bound V hV
  simpa only [referenceParameters_gap] using
    massSquared_lower_bound referenceParameters s V hLower τ x

theorem reference_mass_posDef (s : InternalShifts N) (V : Potential N)
    (hV : ∀ τ x, (V τ x).PosSemidef)
    (τ : ObservedTime) (x : SpatialPosition) :
    (massSquared referenceParameters s V τ x).PosDef := by
  exact posDef_of_lower_bound (reference_mass_lower_bound s V hV τ x) (by norm_num)

/-- 第四章の巡回並進を使い、仮定を満たすデータを任意N≥1で構成する。 -/
def referenceModel (N : ℕ) [NeZero N] : Discretization.FiniteModelData N where
  parameters := referenceParameters
  shifts := Lattice.concreteInternalShifts N
  potential := zeroPotential

theorem referenceModel_stabilityHypotheses :
    StabilityHypotheses (referenceModel N).parameters (referenceModel N).potential :=
  reference_zero_stabilityHypotheses

theorem referenceModel_mass_lower_bound (τ : ObservedTime) (x : SpatialPosition) :
    HasMatrixLowerBound
      (massSquared (referenceModel N).parameters (referenceModel N).shifts
        (referenceModel N).potential τ x) (1 / 9) := by
  exact reference_mass_lower_bound (Lattice.concreteInternalShifts N) zeroPotential
    (fun _ _ => Matrix.PosSemidef.zero) τ x

theorem referenceModel_mass_posDef (τ : ObservedTime) (x : SpatialPosition) :
    (massSquared (referenceModel N).parameters (referenceModel N).shifts
      (referenceModel N).potential τ x).PosDef := by
  exact posDef_of_lower_bound (referenceModel_mass_lower_bound τ x) (by norm_num)

/-- 仮定を同時に満たし、質量行列も正定値となる具体的な模型の存在。 -/
theorem positiveModel_exists (N : ℕ) [NeZero N] :
    ∃ D : Discretization.FiniteModelData N,
      StabilityHypotheses D.parameters D.potential ∧
        ∀ τ x,
          HasMatrixLowerBound (massSquared D.parameters D.shifts D.potential τ x)
              (1 / 9) ∧
            (massSquared D.parameters D.shifts D.potential τ x).PosDef := by
  refine ⟨referenceModel N, referenceModel_stabilityHypotheses, ?_⟩
  intro τ x
  exact ⟨referenceModel_mass_lower_bound τ x, referenceModel_mass_posDef τ x⟩

/-! ## 5.4　スペクトルへの帰結 -/

/-- 下界は固有値一つ一つにも及ぶ。正規化固有ベクトルに二次形式を適用する。 -/
theorem eigenvalues_lower_bound {A : InternalMatrix N} {r : ℝ}
    (hA : A.IsHermitian) (hLower : HasMatrixLowerBound A r) (i : Grid N) :
    r ≤ hA.eigenvalues i := by
  let v : EuclideanSpace ℂ (Grid N) := hA.eigenvectorBasis i
  have hv : RCLike.re (dotProduct (star ⇑v) ⇑v) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K]
    simp [v, hA.eigenvectorBasis.orthonormal.1 i]
  have h := hLower.re_dotProduct_nonneg ⇑v
  simp only [realScalarMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul] at h
  simp only [map_sub, smul_eq_mul, RCLike.mul_re] at h
  have hrRe : RCLike.re (r : ℂ) = r := rfl
  have hrIm : RCLike.im (r : ℂ) = 0 := rfl
  rw [hrRe, hrIm, zero_mul, sub_zero, hv, mul_one] at h
  have hEigen := hA.eigenvalues_eq i
  change hA.eigenvalues i = RCLike.re (dotProduct (star ⇑v) (A.mulVec ⇑v)) at hEigen
  linarith

theorem massSquared_eigenvalues_lower_bound
    (p : ModelParameters) (s : InternalShifts N) (V : Potential N)
    (hV : IsHermitianPotential V) (hLower : HasUniformPotentialLowerBound V p.vMin)
    (τ : ObservedTime) (x : SpatialPosition) (i : Grid N) :
    sufficientMassGap p ≤ (massSquared_hermitian p s V hV τ x).eigenvalues i :=
  eigenvalues_lower_bound (massSquared_hermitian p s V hV τ x)
    (massSquared_lower_bound p s V hLower τ x) i

/-- 具体的な参照模型では、すべての固有値が1/9以上である。 -/
theorem referenceModel_eigenvalues_lower_bound
    (τ : ObservedTime) (x : SpatialPosition) (i : Grid N) :
    (1 / 9 : ℝ) ≤
      (massSquared_hermitian referenceParameters (Lattice.concreteInternalShifts N)
        zeroPotential reference_zero_stabilityHypotheses.hermitian τ x).eigenvalues i := by
  simpa only [referenceParameters_gap] using
    massSquared_eigenvalues_lower_bound referenceParameters (Lattice.concreteInternalShifts N)
      zeroPotential reference_zero_stabilityHypotheses.hermitian
      reference_zero_stabilityHypotheses.lowerBound τ x i

/-- 正の下界を持つ質量二乗行列の固有値は、すべて厳密に正である。 -/
theorem massSquared_eigenvalues_pos
    (p : ModelParameters) (s : InternalShifts N) (V : Potential N)
    (h : StabilityHypotheses p V) (τ : ObservedTime) (x : SpatialPosition)
    (i : Grid N) :
    0 < (massSquared_hermitian p s V h.hermitian τ x).eigenvalues i := by
  exact (massSquared_posDef_of_stabilityHypotheses p s V h τ x).eigenvalues_pos i

/-!
## 証明範囲

* massSquared_hermitian：自己共役なVからM²の自己共役性。
* massSquared_lower_bound：M² ≥ (μ²+vMin-8/a²)I。
* massSquared_posSemidef / massSquared_posDef：非負／正の下界からの帰結。
* reference_mass_lower_bound：a=3、μ=1、V ≥ 0 で M² ≥ (1/9)I。
* positiveModel_exists：具体的な巡回シフトを持つ模型の実在。
* massSquared_eigenvalues_lower_bound：各固有値にも同じ下界δが成り立つ。
* referenceModel_eigenvalues_lower_bound：参照模型の各固有値が1/9以上。
* massSquared_eigenvalues_pos：すべての質量二乗固有値が正であること。

本章の完了条件は自己共役性・正の下界・具体例である。
ロードマップ5.4の追加課題である、巡回格子の離散フーリエ基底の完備性と
各固有値の明示式は、このファイルでは証明していない。
第三章の位相ごとの正弦表示を、それだけで全スペクトルの証明とは扱わない。

行列の正定値性は、場の時間発展の安定性や散乱行列のユニタリティの
証明を代用しない。後続章では正の運動項、解の正則性・境界条件、
時間依存性などを明示して、それぞれの結論を導く。
-/

#print axioms massSquared_hermitian
#print axioms massSquared_lower_bound
#print axioms massSquared_posDef
#print axioms reference_mass_lower_bound
#print axioms positiveModel_exists
#print axioms massSquared_eigenvalues_lower_bound
#print axioms referenceModel_eigenvalues_lower_bound
#print axioms massSquared_eigenvalues_pos

end MassMatrix
end TwelveDimensionalPhaseSpace
