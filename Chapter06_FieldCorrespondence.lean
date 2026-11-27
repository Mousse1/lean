import Chapter05_MassMatrix
import Mathlib.LinearAlgebra.Matrix.Reindex

set_option autoImplicit false

/-!
# 第六章　有限格子場と4次元多成分場の対応

内部格子 Grid N = ZMod N × ZMod N の場を、同じ外部座標 (τ,x) 上の
N²成分複素場へ移す。有限成分の並べ替えであり、外部空間の離散化ではない。
内部の正定値ℓ²内積について線形等長同型を構成する。

場の作用の被積分関数と方程式がこの対応で一致することを示す。
作用積分の可積分性、変分原理からの方程式の導出、解の存在・一意性、
連続12次元理論全体との同値性は、この章の結論に含めない。

## 利用方法と検証環境

第一〜第五章と同じmathlibプロジェクトで使用する。
先行章のコンパイル済みモジュールを配置した後：

    lake env lean -DwarningAsError=true Chapter06_FieldCorrespondence.lean

Lean 4.24.0 / mathlib v4.24.0。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

noncomputable section
open scoped BigOperators ComplexOrder

namespace TwelveDimensionalPhaseSpace
namespace FieldCorrespondence

abbrev ComponentIndex (N : ℕ) := Fin (N ^ 2)
abbrev ComponentVector (N : ℕ) := ComponentIndex N → ℂ
abbrev ComponentHilbert (N : ℕ) := EuclideanSpace ℂ (ComponentIndex N)
abbrev ComponentMatrix (N : ℕ) := Matrix (ComponentIndex N) (ComponentIndex N) ℂ
abbrev FourDField (N : ℕ) := ObservedTime → SpatialPosition → ComponentVector N

/-- 外部の座標は時間1個と空間3個である。 -/
theorem externalCoordinate_finrank :
    Module.finrank ℝ (ObservedTime × SpatialPosition) = 4 := by
  simp [ObservedTime, SpatialPosition, SpaceCoordinates, SpatialIndex]

variable {N : ℕ} [NeZero N]

theorem grid_card : Fintype.card (Grid N) = N ^ 2 := by
  simp [Grid, pow_two]

/-- ZModからFinへの対応と、有限直積の列挙を合成した具体的な添字対応。 -/
def componentIndexEquiv (N : ℕ) [NeZero N] : Grid N ≃ ComponentIndex N :=
  ((Equiv.prodCongr (ZMod.finEquiv N).toEquiv.symm
      (ZMod.finEquiv N).toEquiv.symm).trans finProdFinEquiv).trans
    (finCongr (pow_two N).symm)

def vectorEquiv (N : ℕ) [NeZero N] :
    InternalVector N ≃ₗ[ℂ] ComponentVector N :=
  LinearEquiv.piCongrLeft' ℂ (fun _ : Grid N => ℂ) (componentIndexEquiv N)

@[simp]
theorem vectorEquiv_apply (v : InternalVector N) (j : ComponentIndex N) :
    vectorEquiv N v j = v ((componentIndexEquiv N).symm j) := rfl

@[simp]
theorem vectorEquiv_symm_apply (v : ComponentVector N) (n : Grid N) :
    (vectorEquiv N).symm v n = v (componentIndexEquiv N n) := by
  simp [vectorEquiv, LinearEquiv.piCongrLeft']

/-- 関数型の上限ノルムではなく、ℓ²ノルムを持つ型の間の等長同型。 -/
def hilbertEquiv (N : ℕ) [NeZero N] :
    InternalHilbert N ≃ₗᵢ[ℂ] ComponentHilbert N :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (componentIndexEquiv N)

theorem hilbertEquiv_coordinates (v : InternalVector N) :
    hilbertEquiv N (WithLp.toLp 2 v) = WithLp.toLp 2 (vectorEquiv N v) := rfl

theorem hilbertEquiv_norm (v : InternalHilbert N) :
    ‖hilbertEquiv N v‖ = ‖v‖ := (hilbertEquiv N).norm_map v

theorem hilbertEquiv_inner (u v : InternalHilbert N) :
    inner ℂ (hilbertEquiv N u) (hilbertEquiv N v) = inner ℂ u v :=
  (hilbertEquiv N).inner_map_map u v

omit [NeZero N] in
theorem componentHilbert_finrank :
    Module.finrank ℂ (ComponentHilbert N) = N ^ 2 := by
  simp [ComponentHilbert, ComponentIndex]

/-- 各外部点で同じ添字対応を使う。大域的な場のノルムはここでは導入しない。 -/
def fieldEquiv (N : ℕ) [NeZero N] : CoordinateField N ≃ₗ[ℂ] FourDField N where
  toFun φ τ x j := φ τ x ((componentIndexEquiv N).symm j)
  invFun Φ τ x n := Φ τ x (componentIndexEquiv N n)
  left_inv φ := by funext τ x n; simp
  right_inv Φ := by funext τ x j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem fieldEquiv_apply (φ : CoordinateField N) (τ : ObservedTime)
    (x : SpatialPosition) (j : ComponentIndex N) :
    fieldEquiv N φ τ x j = φ τ x ((componentIndexEquiv N).symm j) := rfl

theorem fieldEquiv_at (φ : CoordinateField N) (τ : ObservedTime) (x : SpatialPosition) :
    fieldEquiv N φ τ x = vectorEquiv N (φ τ x) := rfl

/-! ### 補助：行列作用の対応 -/

def matrixEquiv (N : ℕ) [NeZero N] :
    InternalMatrix N ≃ₐ[ℂ] ComponentMatrix N :=
  Matrix.reindexAlgEquiv ℂ ℂ (componentIndexEquiv N)

@[simp]
theorem matrixEquiv_apply (A : InternalMatrix N) (i j : ComponentIndex N) :
    matrixEquiv N A i j =
      A ((componentIndexEquiv N).symm i) ((componentIndexEquiv N).symm j) := rfl

/-- 一般の内部作用素について、対応が行列作用を保つ。 -/
theorem matrixEquiv_mulVec (A : InternalMatrix N) (v : InternalVector N) :
    (matrixEquiv N A).mulVec (vectorEquiv N v) = vectorEquiv N (A.mulVec v) := by
  ext j
  change (∑ i : ComponentIndex N,
    A ((componentIndexEquiv N).symm j) ((componentIndexEquiv N).symm i) *
      v ((componentIndexEquiv N).symm i)) =
    ∑ n : Grid N, A ((componentIndexEquiv N).symm j) n * v n
  exact (componentIndexEquiv N).symm.sum_comp
    (fun n => A ((componentIndexEquiv N).symm j) n * v n)

theorem matrixEquiv_adjoint (A : InternalMatrix N) :
    matrixEquiv N A.conjTranspose = (matrixEquiv N A).conjTranspose := rfl

theorem matrixEquiv_hermitian {A : InternalMatrix N} (hA : A.IsHermitian) :
    (matrixEquiv N A).IsHermitian := by
  change (matrixEquiv N A).conjTranspose = matrixEquiv N A
  rw [← matrixEquiv_adjoint, hA.eq]

theorem matrixEquiv_unitary {U : InternalMatrix N} (hU : IsUnitaryMatrix U) :
    IsUnitaryMatrix (matrixEquiv N U) := by
  constructor
  · rw [← matrixEquiv_adjoint, ← map_mul, hU.1, map_one]
  · rw [← matrixEquiv_adjoint, ← map_mul, hU.2, map_one]

/-- シフトも対称性生成子も、同じ一般的な作用の対応に従う。 -/
theorem matrixEquiv_commute {A B : InternalMatrix N} (h : A * B = B * A) :
    matrixEquiv N A * matrixEquiv N B = matrixEquiv N B * matrixEquiv N A := by
  rw [← map_mul, ← map_mul, h]

/-! ## 6.2　被積分関数と場の方程式 -/

/-- 正の内部内積に対応する成分和。第一引数に複素共役を取る。 -/
def pairing {ι : Type*} [Fintype ι] (u v : ι → ℂ) : ℂ :=
  dotProduct (star u) v

def squaredNorm {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  (pairing v v).re

/-- 作用密度の運動項に使う成分和が、正のℓ²ノルムの二乗と一致する。 -/
theorem squaredNorm_eq_hilbertNorm {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    squaredNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ ^ 2 := by
  unfold squaredNorm pairing
  rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, inner_self_eq_norm_sq_to_K]
  change RCLike.re
    ((RCLike.ofReal ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ : ℂ) ^ 2) = _
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]

theorem squaredNorm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    0 ≤ squaredNorm v := by
  rw [squaredNorm_eq_hilbertNorm]
  exact sq_nonneg _

/-- 自己共役な質量行列の二次形式に虚部はない。 -/
theorem hermitian_quadratic_im_zero {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (u : ι → ℂ) :
    (pairing u (A.mulVec u)).im = 0 :=
  hA.im_star_dotProduct_mulVec_self u

theorem pairing_vectorEquiv (u v : InternalVector N) :
    pairing (vectorEquiv N u) (vectorEquiv N v) = pairing u v := by
  change (∑ j : ComponentIndex N,
    star (u ((componentIndexEquiv N).symm j)) * v ((componentIndexEquiv N).symm j)) =
    ∑ n : Grid N, star (u n) * v n
  exact (componentIndexEquiv N).symm.sum_comp (fun n => star (u n) * v n)

theorem squaredNorm_vectorEquiv (v : InternalVector N) :
    squaredNorm (vectorEquiv N v) = squaredNorm v := by
  simp only [squaredNorm, pairing_vectorEquiv]

/-- 配置、時間微分、空間微分を独立に与えた作用密度。
自己共役な質量行列に対して質量二次形式は実数であり、その実部を用いる。 -/
def lagrangianJet {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (u timeJet : ι → ℂ) (spaceJet : SpatialIndex → ι → ℂ) : ℝ :=
  squaredNorm timeJet - (∑ k : SpatialIndex, squaredNorm (spaceJet k)) -
    (pairing u (A.mulVec u)).re

theorem lagrangianJet_correspondence (A : InternalMatrix N)
    (u timeJet : InternalVector N) (spaceJet : SpatialIndex → InternalVector N) :
    lagrangianJet (matrixEquiv N A) (vectorEquiv N u) (vectorEquiv N timeJet)
      (fun k => vectorEquiv N (spaceJet k)) = lagrangianJet A u timeJet spaceJet := by
  simp only [lagrangianJet, squaredNorm_vectorEquiv, matrixEquiv_mulVec, pairing_vectorEquiv]

/-- 以下の微分は各成分についての実変数微分。 -/
def timeDerivative {ι : Type*} (Φ : ObservedTime → SpatialPosition → ι → ℂ)
    (τ : ObservedTime) (x : SpatialPosition) : ι → ℂ :=
  fun i => deriv (fun t : ℝ => Φ t x i) τ

def spaceDerivative {ι : Type*} (Φ : ObservedTime → SpatialPosition → ι → ℂ)
    (τ : ObservedTime) (x : SpatialPosition) (k : SpatialIndex) : ι → ℂ :=
  fun i => deriv (fun r : ℝ => Φ τ (Function.update x k r) i) (x k)

theorem timeDerivative_correspondence (φ : CoordinateField N)
    (τ : ObservedTime) (x : SpatialPosition) :
    timeDerivative (fieldEquiv N φ) τ x = vectorEquiv N (timeDerivative φ τ x) := rfl

theorem spaceDerivative_correspondence (φ : CoordinateField N)
    (τ : ObservedTime) (x : SpatialPosition) (k : SpatialIndex) :
    spaceDerivative (fieldEquiv N φ) τ x k = vectorEquiv N (spaceDerivative φ τ x k) := rfl

/-- 成分表示で、同じシフトとポテンシャルから独立に質量行列を組み立てる。 -/
def componentLaplacian (p : ModelParameters) (s : InternalShifts N) : ComponentMatrix N :=
  (p.latticeSpacing ^ 2)⁻¹ •
    (((2 : ℂ) • 1 - matrixEquiv N s.first - (matrixEquiv N s.first).conjTranspose) +
      ((2 : ℂ) • 1 - matrixEquiv N s.second - (matrixEquiv N s.second).conjTranspose))

def componentMassSquared (D : Discretization.FiniteModelData N)
    (τ : ObservedTime) (x : SpatialPosition) : ComponentMatrix N :=
  ((D.parameters.massParameter ^ 2 : ℝ) : ℂ) • 1 -
    componentLaplacian D.parameters D.shifts + matrixEquiv N (D.potential τ x)

theorem matrixEquiv_real_smul (r : ℝ) (A : InternalMatrix N) :
    matrixEquiv N (r • A) = r • matrixEquiv N A := rfl

theorem matrixEquiv_internalLaplacian (p : ModelParameters) (s : InternalShifts N) :
    matrixEquiv N (internalLaplacian p s) = componentLaplacian p s := by
  simp only [internalLaplacian, componentLaplacian, matrixEquiv_real_smul,
    map_add, map_sub, map_smul, map_one, matrixEquiv_adjoint]

theorem matrixEquiv_massSquared (D : Discretization.FiniteModelData N)
    (τ : ObservedTime) (x : SpatialPosition) :
    matrixEquiv N (massSquared D.parameters D.shifts D.potential τ x) =
      componentMassSquared D τ x := by
  simp only [massSquared, freeMassSquared, realScalarMatrix, componentMassSquared,
    map_add, map_sub, map_smul, map_one, matrixEquiv_internalLaplacian]

def latticeLagrangianDensity (D : Discretization.FiniteModelData N)
    (φ : CoordinateField N) (τ : ObservedTime) (x : SpatialPosition) : ℝ :=
  lagrangianJet (massSquared D.parameters D.shifts D.potential τ x) (φ τ x)
    (timeDerivative φ τ x) (spaceDerivative φ τ x)

def componentLagrangianDensity (D : Discretization.FiniteModelData N)
    (Φ : FourDField N) (τ : ObservedTime) (x : SpatialPosition) : ℝ :=
  lagrangianJet (componentMassSquared D τ x) (Φ τ x)
    (timeDerivative Φ τ x) (spaceDerivative Φ τ x)

/-- 作用積分を取る前の、被積分関数そのものの一致。 -/
theorem lagrangianDensity_correspondence (D : Discretization.FiniteModelData N)
    (φ : CoordinateField N) (τ : ObservedTime) (x : SpatialPosition) :
    componentLagrangianDensity D (fieldEquiv N φ) τ x = latticeLagrangianDensity D φ τ x := by
  unfold componentLagrangianDensity latticeLagrangianDensity
  rw [← matrixEquiv_massSquared, fieldEquiv_at, timeDerivative_correspondence]
  have hspace : spaceDerivative (fieldEquiv N φ) τ x =
      fun k => vectorEquiv N (spaceDerivative φ τ x k) := by
    funext k
    exact spaceDerivative_correspondence φ τ x k
  rw [hspace]
  exact lagrangianJet_correspondence _ _ _ _

/-- 第三章の方程式を、N²成分の行列表示で独立に記述する。 -/
def componentFieldResidual (D : Discretization.FiniteModelData N)
    (Φ : FourDField N) (τ : ObservedTime) (x : SpatialPosition)
    (i : ComponentIndex N) : ℂ :=
  deriv (deriv (fun t : ℝ => Φ t x i)) τ -
    (∑ k : SpatialIndex,
      deriv (deriv (fun r : ℝ => Φ τ (Function.update x k r) i)) (x k)) +
    (componentMassSquared D τ x).mulVec (Φ τ x) i

def ComponentFieldEquation (D : Discretization.FiniteModelData N) (Φ : FourDField N) : Prop :=
  ∀ τ x i, componentFieldResidual D Φ τ x i = 0

theorem fieldResidual_correspondence (D : Discretization.FiniteModelData N)
    (φ : CoordinateField N) (τ : ObservedTime) (x : SpatialPosition)
    (j : ComponentIndex N) :
    componentFieldResidual D (fieldEquiv N φ) τ x j =
      Discretization.adoptedFieldResidual D φ τ x ((componentIndexEquiv N).symm j) := by
  unfold componentFieldResidual
  rw [← matrixEquiv_massSquared, fieldEquiv_at, matrixEquiv_mulVec]
  rfl

/-- 解の方程式を満たすことの必要十分な対応。解の存在は仮定も結論もしていない。 -/
theorem fieldEquation_iff (D : Discretization.FiniteModelData N) (φ : CoordinateField N) :
    Discretization.AdoptedFieldEquation D φ ↔ ComponentFieldEquation D (fieldEquiv N φ) := by
  constructor
  · intro h τ x j
    rw [fieldResidual_correspondence]
    exact h τ x ((componentIndexEquiv N).symm j)
  · intro h τ x n
    have hj := h τ x (componentIndexEquiv N n)
    rw [fieldResidual_correspondence] at hj
    simpa only [Equiv.symm_apply_apply] using hj

/-- 時間と各空間座標方向の線に沿ったC²条件。大域的な関数空間の条件ではない。 -/
def SliceC2 {ι : Type*} (Φ : ObservedTime → SpatialPosition → ι → ℂ) : Prop :=
  (∀ x i, ContDiff ℝ 2 (fun τ : ℝ => Φ τ x i)) ∧
    ∀ τ x k i, ContDiff ℝ 2 (fun r : ℝ => Φ τ (Function.update x k r) i)

/-- 微分式を古典的な方程式として読むための、このC²条件も保存される。 -/
theorem sliceC2_iff (φ : CoordinateField N) : SliceC2 φ ↔ SliceC2 (fieldEquiv N φ) := by
  constructor
  · rintro ⟨htime, hspace⟩
    exact ⟨fun x j => htime x ((componentIndexEquiv N).symm j),
      fun τ x k j => hspace τ x k ((componentIndexEquiv N).symm j)⟩
  · rintro ⟨htime, hspace⟩
    constructor
    · intro x n
      simpa only [fieldEquiv_apply, Equiv.symm_apply_apply] using
        htime x (componentIndexEquiv N n)
    · intro τ x k n
      simpa only [fieldEquiv_apply, Equiv.symm_apply_apply] using
        hspace τ x k (componentIndexEquiv N n)

/-- 指定したC²条件を持ち方程式を満たすことが、両表示で同値である。 -/
theorem classicalSolution_iff (D : Discretization.FiniteModelData N) (φ : CoordinateField N) :
    (SliceC2 φ ∧ Discretization.AdoptedFieldEquation D φ) ↔
      (SliceC2 (fieldEquiv N φ) ∧ ComponentFieldEquation D (fieldEquiv N φ)) :=
  and_congr (sliceC2_iff φ) (fieldEquation_iff D φ)

/-! ## 6.3　保存する構造と、第五章の下界との接続 -/

theorem matrixEquiv_posSemidef {A : InternalMatrix N} (hA : A.PosSemidef) :
    (matrixEquiv N A).PosSemidef :=
  hA.submatrix (componentIndexEquiv N).symm

theorem matrixEquiv_posDef {A : InternalMatrix N} (hA : A.PosDef) :
    (matrixEquiv N A).PosDef := by
  refine ⟨matrixEquiv_hermitian hA.isHermitian, ?_⟩
  intro v hv
  obtain ⟨u, rfl⟩ := (vectorEquiv N).surjective v
  have hu : u ≠ 0 := by
    intro hz
    apply hv
    simp only [hz, map_zero]
  change 0 < pairing (vectorEquiv N u) ((matrixEquiv N A).mulVec (vectorEquiv N u))
  rw [matrixEquiv_mulVec, pairing_vectorEquiv]
  exact hA.2 u hu

def HasComponentLowerBound (A : ComponentMatrix N) (r : ℝ) : Prop :=
  (A - (r : ℂ) • 1).PosSemidef

theorem matrixEquiv_lower_bound {A : InternalMatrix N} {r : ℝ}
    (hA : HasMatrixLowerBound A r) : HasComponentLowerBound (matrixEquiv N A) r := by
  have h := matrixEquiv_posSemidef hA
  simpa only [HasComponentLowerBound, realScalarMatrix, map_sub, map_smul, map_one] using h

theorem componentMassSquared_lower_bound (D : Discretization.FiniteModelData N)
    (hV : HasUniformPotentialLowerBound D.potential D.parameters.vMin)
    (τ : ObservedTime) (x : SpatialPosition) :
    HasComponentLowerBound (componentMassSquared D τ x) (sufficientMassGap D.parameters) := by
  rw [← matrixEquiv_massSquared]
  exact matrixEquiv_lower_bound
    (MassMatrix.massSquared_lower_bound D.parameters D.shifts D.potential hV τ x)

theorem componentMassSquared_posDef (D : Discretization.FiniteModelData N)
    (h : StabilityHypotheses D.parameters D.potential)
    (τ : ObservedTime) (x : SpatialPosition) :
    (componentMassSquared D τ x).PosDef := by
  rw [← matrixEquiv_massSquared]
  exact matrixEquiv_posDef
    (MassMatrix.massSquared_posDef_of_stabilityHypotheses
      D.parameters D.shifts D.potential h τ x)

theorem shift_action_correspondence (s : InternalShifts N) (v : InternalVector N) :
    (matrixEquiv N s.first).mulVec (vectorEquiv N v) = vectorEquiv N (s.first.mulVec v) ∧
      (matrixEquiv N s.second).mulVec (vectorEquiv N v) = vectorEquiv N (s.second.mulVec v) :=
  ⟨matrixEquiv_mulVec s.first v, matrixEquiv_mulVec s.second v⟩

/-- 同じ対称性を両表示で表したとき、質量行列との可換性も保たれる。 -/
theorem symmetry_mass_commute (p : ModelParameters) (s : InternalShifts N)
    (V : Potential N) (Q : InternalMatrix N) (h : SymmetryHypotheses p s V Q)
    (τ : ObservedTime) (x : SpatialPosition) :
    matrixEquiv N Q * matrixEquiv N (massSquared p s V τ x) =
      matrixEquiv N (massSquared p s V τ x) * matrixEquiv N Q := by
  apply matrixEquiv_commute
  simp only [massSquared, Matrix.mul_add, Matrix.add_mul, h.freeCommute,
    h.interactionCommute τ x]

/-!
## 証明範囲

* componentIndexEquiv / hilbertEquiv / fieldEquiv：具体的な有限成分対応。
* externalCoordinate_finrank / componentHilbert_finrank：外部4座標、内部N²成分。
* hilbertEquiv_norm / hilbertEquiv_inner：正定値ℓ²構造の保存。
* squaredNorm_eq_hilbertNorm / squaredNorm_nonneg：標準的な正の運動項。
* hermitian_quadratic_im_zero：自己共役な質量行列の二次形式が実数であること。
* matrixEquiv_mulVec / shift_action_correspondence：行列作用・内部シフトの対応。
* matrixEquiv_massSquared：同じデータから組み立てた質量作用素の一致。
* lagrangianDensity_correspondence：微分項を含む作用密度の一致。
* fieldEquation_iff / sliceC2_iff / classicalSolution_iff：方程式と線に沿うC²条件の対応。
* componentMassSquared_lower_bound / componentMassSquared_posDef：第五章の評価の移送。
* matrixEquiv_unitary / symmetry_mass_commute：ユニタリ性・残存対称性の保存。

Leanのderivは全関数について定義される。本章の微分式の一致は、
関数が同じであることに由来するため、C²条件なしにも成立する。
古典的な方程式としての解釈には、ここで保存を示したSliceC2などの
正則性を別途要求する。作用積分、変分原理、場の解の存在・安定性、
散乱解や散乱行列の構成は後続の証明課題である。

連続12次元模型から有限模型を得るための模型化の選択を、
この有限次元の同型によって正当化したとは主張しない。
-/

#print axioms hilbertEquiv
#print axioms hilbertEquiv_inner
#print axioms squaredNorm_eq_hilbertNorm
#print axioms hermitian_quadratic_im_zero
#print axioms matrixEquiv_mulVec
#print axioms matrixEquiv_massSquared
#print axioms lagrangianDensity_correspondence
#print axioms fieldEquation_iff
#print axioms sliceC2_iff
#print axioms classicalSolution_iff
#print axioms componentMassSquared_lower_bound
#print axioms componentMassSquared_posDef
#print axioms symmetry_mass_commute

end FieldCorrespondence
end TwelveDimensionalPhaseSpace
