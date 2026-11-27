import Chapter01_Definitions
import Chapter02_CanonicalStructure
import Chapter03_Discretization
import Chapter04_PeriodicLattice
import Chapter05_MassMatrix
import Chapter06_FieldCorrespondence
import Chapter07_EnergyStability
import Chapter08_StaticScattering
import Chapter09_WronskianFlux
import Chapter10_ScatteringUnitarity
import Chapter11_InternalSymmetry

set_option autoImplicit false
/-!
# 第十二章　主定理の統合と証明の検査

## 三つの主定理と、その射程

本章は第一〜第十一章をインポートし、そこで証明した結論を次の三群にまとめる。
Certificateは結論の束を表すPropであり、主定理への入力として仮定するものではない。
各主定理が、その全フィールドの証明を構成する。

| 主定理 | 明示した仮定 | 証明した結論 |
|---|---|---|
| main_fourDimensional_correspondence | 採用した有限模型のデータ | 外部4次元・内部N²成分、質量行列とラグランジアン密度の対応、正則性を含む方程式の同値性 |
| main_finiteMode_stability | 一定の質量行列M≥δI、δ>0、固定空間波数k | 任意初期値からの大域解の存在・一意性、エネルギー保存、時刻によらない変位・速度の評価 |
| main_finiteLayer_scattering | 自己共役有限層障壁、全外部チャネルが開くこと | 散乱解と散乱行列の存在・一意性、流束保存、流束規格化後の両側ユニタリティ、残存対称性の継承と選択則 |

4次元表示の定理は、採用した有限内部格子場の表示の対応である。
連続な12次元理論を有限模型へ量子化・縮約する写像の構成とは区別する。
ラグランジアン密度の一致は、積分や変分の正当化まで含まない。

## 安定性について未完了の部分

第七章で証明した存在定理は、有界対称作用素の振動系と、一定質量行列を持つ
各固定空間波数モードについてのものである。
一般の空間依存行列値ポテンシャルを持つ -Δ+M²(x) について、
L²上の定義域・自己共役性・有限エネルギー解の存在はまだ構成していない。
従ってロードマップの「空間連続の場全体の存在と線形安定性」は未完了である。

main_domain_strong_solution_estimateは、指定した定義域D、対称作用素A、下界、
およびIsStrongDomainWaveを満たす十分に正則な解を入力とする条件付き定理である。
この解の条件には (Au)'=Av も含まれる。
この定理から、そのような解が任意初期値に対して存在するとは結論しない。
各波数の解を積分した場全体の存在、正周波数ユニタリ群、非線形安定性も含めない。

## 散乱について構成できた部分

第十章のIsScatteringSolutionを変更せず、任意の入射振幅に対する
出射振幅と全実数上の関数y=(f,f')の組が一意に存在することを含む。
接続点での連続性と、接続点以外での微分方程式を含む。
散乱行列Sは端点条件から実際に構成したものを使う。

    SF = W S W⁻¹、W = diag(K^(1/2),K^(1/2))
    SF† SF = I、SF SF† = I

であり、未規格化Sの通常のユニタリティと取り違えない。
残存対称性Qについては、第一章のSymmetryHypothesesを入力にした条件付きの結論を持つ。
この条件はQのユニタリ性、自由質量行列との可換性、相互作用との可換性である。
禁止遷移や散乱行列との可換性自体を仮定には含めない。

main_reference_scatteringは、任意N≥1の具体的な巡回格子と、
第十一章の第一方向変調・対角方向変調の障壁に一般定理を適用する。
参照値a=3、μ=1、ω=2、横方向運動量0で、全開チャネル条件も証明済みである。
具体的なs・r-s mod Nの選択則は第十一章の定理としてそのまま利用できる。

## 12次元構造と4次元の拘束について

本章の安定性・散乱の主定理は、有限行列と明示した解析条件から導かれる。
正準12次元相空間や独立した三時間発展を、これらの主定理の仮定には置かない。
同梱のProofAuditは、主定理の宣言・証明項のプロジェクト内依存を探索し、
Canonical名前空間やPhasePoint等への依存がないことを検査する。
モジュールがインポートされていることと、個別定理の証明依存は区別する。

さらにunrestricted_hermitian_mass_realizableでは、Vを任意の自己共役行列値関数から
選べる場合、任意の自己共役行列AをM₀²+Vとして実現できることを証明する。
従って、その自由度を制限しなければ、質量行列の形だけから4次元模型への
非自明な制約があるとは結論できない。これは任意のVを許すクラスについての定理であり、
散乱章の外部でV=0という有限層障壁条件まで満たすと主張するものではない。
局所性・相互作用の許容クラス・対称性・連続極限の追加条件は別の研究課題である。

## 検証と利用方法

同梱の再現用プロジェクトでは、第一〜第十二章とProofAuditをルートに含めて：

    lake build

を実行する。warningAsErrorを有効にし、未完成証明の逃げ道のソース検査と、
主定理の公理依存・正準構造への宣言依存の検査も用意する。
これは通常のLeanカーネルでの検証と依存検査であり、独立実装の証明検査器による再検証ではない。

既存のmathlibプロジェクトで、このファイルだけを使用する場合は、
第一〜第十一章を先にコンパイルしてから：

    lake env lean -DwarningAsError=true Chapter12_MainTheorems.lean

Lean 4.24.0 / mathlib v4.24.0。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
末尾の #print axioms で主要定理の公理依存を表示する。
-/

noncomputable section
open scoped BigOperators ComplexOrder
namespace TwelveDimensionalPhaseSpace
namespace MainTheorems
open Discretization FieldCorrespondence EnergyStability StaticScattering
open WronskianFlux ScatteringUnitarity InternalSymmetry

/-! ## 12.1　有限模型の4次元表示と質量行列の評価 -/

section FiniteModelCorrespondence
variable {N : ℕ} [NeZero N]

structure FourDimensionalCertificate (D : FiniteModelData N) : Prop where
  externalDimension : Module.finrank ℝ (ObservedTime × SpatialPosition) = 4
  internalDimension : Module.finrank ℂ (ComponentHilbert N) = N ^ 2
  massCorrespondence : ∀ τ x,
    matrixEquiv N (massSquared D.parameters D.shifts D.potential τ x) = componentMassSquared D τ x
  densityCorrespondence : ∀ φ τ x,
    componentLagrangianDensity D (fieldEquiv N φ) τ x = latticeLagrangianDensity D φ τ x
  classicalEquation : ∀ φ,
    (SliceC2 φ ∧ AdoptedFieldEquation D φ) ↔
      (SliceC2 (fieldEquiv N φ) ∧ ComponentFieldEquation D (fieldEquiv N φ))

theorem main_fourDimensional_correspondence (D : FiniteModelData N) : FourDimensionalCertificate D :=
  ⟨externalCoordinate_finrank, componentHilbert_finrank, matrixEquiv_massSquared D,
    lagrangianDensity_correspondence D, classicalSolution_iff D⟩

theorem main_mass_lower_bound (D : FiniteModelData N)
    (hV : HasUniformPotentialLowerBound D.potential D.parameters.vMin) :
    ∀ τ x, HasComponentLowerBound (componentMassSquared D τ x) (sufficientMassGap D.parameters) :=
  componentMassSquared_lower_bound D hV

theorem main_mass_positive (D : FiniteModelData N)
    (h : StabilityHypotheses D.parameters D.potential) :
    ∀ τ x, (componentMassSquared D τ x).PosDef :=
  componentMassSquared_posDef D h

end FiniteModelCorrespondence

/-! ## 12.2　有限成分・各固定波数モードの存在と安定性 -/

section FiniteModeStability
variable {N : ℕ} [NeZero N]

local instance modeRealInner : InnerProductSpace ℝ (InternalHilbert N) :=
  InnerProductSpace.complexToReal

structure FiniteModeCertificate (M : InternalMatrix N) (k : SpatialMomenta) (δ : ℝ) : Prop where
  solution : ∀ u0 v0 : InternalHilbert N,
    ∃! z : ℝ → InternalHilbert N × InternalHilbert N,
      z 0 = (u0, v0) ∧ IsOscillator (matrixOperator (waveMatrix M k))
        (fun t => (z t).1) (fun t => (z t).2)
  conservedEnergy : ∀ u v : ℝ → InternalHilbert N,
    IsOscillator (matrixOperator (waveMatrix M k)) u v → ∀ t s,
      energy (matrixOperator (waveMatrix M k)) (u t) (v t) =
        energy (matrixOperator (waveMatrix M k)) (u s) (v s)
  uniformBound : ∀ u v : ℝ → InternalHilbert N,
    IsOscillator (matrixOperator (waveMatrix M k)) u v → ∀ t,
      ‖v t‖ ^ 2 + (waveNumberSquared k + δ) * ‖u t‖ ^ 2 ≤
        2 * energy (matrixOperator (waveMatrix M k)) (u 0) (v 0)
  displacementVelocityBounds : ∀ u v : ℝ → InternalHilbert N,
    IsOscillator (matrixOperator (waveMatrix M k)) u v → ∀ t,
      ‖v t‖ ^ 2 ≤ 2 * energy (matrixOperator (waveMatrix M k)) (u 0) (v 0) ∧
      ‖u t‖ ^ 2 ≤ 2 * energy (matrixOperator (waveMatrix M k)) (u 0) (v 0) /
        (waveNumberSquared k + δ)

theorem main_finiteMode_stability (M : InternalMatrix N) (k : SpatialMomenta) (δ : ℝ)
    (hM : HasMatrixLowerBound M δ) (hδ : 0 < δ) : FiniteModeCertificate M k δ := by
  have hLower := waveMatrix_lower_bound M k δ hM
  have hSym := matrixOperator_symmetric (MassMatrix.hermitian_of_lower_bound hLower)
  have hPos : 0 < waveNumberSquared k + δ :=
    add_pos_of_nonneg_of_pos (waveNumberSquared_nonneg k) hδ
  refine ⟨freeMode_exists_unique M k δ hM hδ, ?_, freeMode_stability_bound M k δ hM, ?_⟩
  · intro u v h t s
    exact energy_conserved _ hSym u v h t s
  · intro u v h t
    exact stability_bounds_separate _ hSym _ hPos (matrixOperator_lower_bound hLower) u v h t

theorem main_reference_finiteMode_stability (N : ℕ) [NeZero N] (k : SpatialMomenta) :
    FiniteModeCertificate (referenceFreeMass N) k (1 / 9) :=
  main_finiteMode_stability _ k _ referenceFreeMass_lower_bound (by norm_num)

end FiniteModeStability

/-! ## 非有界作用素の定義域上で、強解を仮定した条件付き評価 -/

section ConditionalDomainEstimate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem main_domain_strong_solution_estimate (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (hA : DomainSymmetric D A) (δ : ℝ) (hLower : DomainLowerBound D A δ)
    (u v : ℝ → D) (h : IsStrongDomainWave D A u v) :
    (∀ t s, domainEnergy D A (u t) (v t) = domainEnergy D A (u s) (v s)) ∧
      (∀ t, ‖(v t : E)‖ ^ 2 + δ * ‖(u t : E)‖ ^ 2 ≤ 2 * domainEnergy D A (u 0) (v 0)) :=
  ⟨domain_energy_conserved D A hA u v h, domain_stability_bound D A hA δ hLower u v h⟩

end ConditionalDomainEstimate

/-! ## 12.3　有限層散乱の存在、一意性、ユニタリティ、選択則 -/

section ScatteringCertificate
variable {N : ℕ} [NeZero N]

structure FiniteScatteringCertificate (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) : Prop where
  solution : ∀ a : StateVector N,
    ∃! sol : StateVector N × (ℝ → StateVector N),
      IsScatteringSolution p s k layers ⟨a, sol.1⟩ sol.2
  matrixUnique : ∃! S : ScatteringMatrix N, ∀ a : StateVector N,
    ∃ y : ℝ → StateVector N, IsScatteringSolution p s k layers ⟨a, S.mulVec a⟩ y
  constructedMatrix : ∀ a : StateVector N,
    ∃ y : ℝ → StateVector N,
      IsScatteringSolution p s k layers ⟨a, (scatteringMatrix p s k layers hOpen).mulVec a⟩ y
  fluxConserved : ∀ a : StateVector N,
    channelNorm p s k ((scatteringMatrix p s k layers hOpen).mulVec a) = channelNorm p s k a
  twoSidedUnitary : IsFluxUnitary (fluxNormalizedScatteringMatrix p s k layers hOpen)
  residualSymmetry : ∀ Q : InternalMatrix N,
    SymmetryHypotheses p s (potentialFromLayers layers) Q →
      fluxNormalizedScatteringMatrix p s k layers hOpen * scatteringSymmetry p s k Q =
        scatteringSymmetry p s k Q * fluxNormalizedScatteringMatrix p s k layers hOpen
  selectionRule : ∀ (Q : InternalMatrix N),
    SymmetryHypotheses p s (potentialFromLayers layers) Q → ∀ (u v : StateVector N) (η ζ : ℂ),
      (scatteringSymmetry p s k Q).mulVec u = η • u →
      (scatteringSymmetry p s k Q).mulVec v = ζ • v → ζ ≠ η →
      star u ⬝ᵥ ((fluxNormalizedScatteringMatrix p s k layers hOpen).mulVec v) = 0

theorem main_finiteLayer_scattering (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) : FiniteScatteringCertificate p s k layers hOpen := by
  refine ⟨scattering_solution_exists_unique p s k layers hOpen,
    scatteringMatrix_exists_unique_for_solutions p s k layers hOpen, ?_,
    scatteringMatrix_preserves_channelNorm p s k layers hOpen,
    fluxNormalizedScatteringMatrix_unitary p s k layers hOpen, ?_, ?_⟩
  · intro a
    exact ⟨_, scatteringMatrix_solution_exists p s k layers hOpen a⟩
  · intro Q hQ
    exact fluxNormalizedScatteringMatrix_commutes p s k layers hOpen Q hQ
  · intro Q hQ u v η ζ hu hv hne
    exact scattering_eigenvalue_transition_zero p s k layers hOpen Q hQ u v η ζ hu hv hne

theorem main_reference_scattering (N : ℕ) [NeZero N] (profiles : List (ScalarLayerProfile N)) :
    FiniteScatteringCertificate referenceParameters (Lattice.concreteInternalShifts N)
      referenceScatteringParameters (profiles.map firstModulatedLayer) (referenceChannelsOpen N) ∧
    FiniteScatteringCertificate referenceParameters (Lattice.concreteInternalShifts N)
      referenceScatteringParameters (profiles.map diagonalModulatedLayer) (referenceChannelsOpen N) :=
  ⟨main_finiteLayer_scattering _ _ _ _ _, main_finiteLayer_scattering _ _ _ _ _⟩

end ScatteringCertificate

/-! ## 12.4　任意の相互作用を許す場合の質量行列の自由度 -/

section BoundaryOfClaims
variable {N : ℕ} [NeZero N]

theorem unrestricted_hermitian_mass_realizable (p : ModelParameters) (s : InternalShifts N)
    (A : InternalMatrix N) (hA : A.IsHermitian) :
    ∃ V : Potential N, IsHermitianPotential V ∧ ∀ τ x, massSquared p s V τ x = A := by
  refine ⟨fun _ _ => A - freeMassSquared p s, ?_, ?_⟩
  · exact fun _ _ => hA.sub (MassMatrix.freeMassSquared_hermitian p s)
  · intro τ x
    change freeMassSquared p s + (A - freeMassSquared p s) = A
    abel

end BoundaryOfClaims
/-!
## 12.5　証明状況の台帳

| 対象 | 状況 |
|---|---|
| 多項式観測量での正準構造、Poisson括弧、質量殻の保存 | 第二章の指定クラスで証明済み |
| 採用した有限差分記号と連続二次式との差、有限次元CCRの障害 | 第三章で証明済み |
| 周期格子の具体的シフト、ラプラシアン上下界、質量行列下界 | 第四・第五章で証明済み |
| 有限模型と外部4次元N²成分表示 | 第六章で証明済み |
| 有界振動系・一定質量の各波数モードの解の存在と一意性 | 第七章で証明済み |
| 定義域上の十分に正則な強解のエネルギー保存と評価 | 解と解析条件を入力とする条件付き定理 |
| 空間連続の場全体の有限エネルギー初期値問題 | 定義域・自己共役性・存在の構成が未完了 |
| 有限層・全開チャネルの定常散乱 | 第八〜第十章で存在・一意性・ユニタリティまで証明済み |
| 残存対称性の選択則、具体的なs・r-s mod Nの保存 | 第十一章で証明済み |
| 独立した三時間発展の整合性、時計の同定、追加時間の観測的識別 | 本検証の結論には含めない |

この台帳の「未完了」は、その命題が数学的に偽であるという主張ではない。
以下は証明済み定理の公理依存の表示であり、新しい公理の宣言ではない。
-/

#print axioms main_fourDimensional_correspondence
#print axioms main_mass_lower_bound
#print axioms main_mass_positive
#print axioms main_finiteMode_stability
#print axioms main_reference_finiteMode_stability
#print axioms main_domain_strong_solution_estimate
#print axioms main_finiteLayer_scattering
#print axioms main_reference_scattering
#print axioms unrestricted_hermitian_mass_realizable

end MainTheorems
end TwelveDimensionalPhaseSpace
