import Chapter09_WronskianFlux

set_option autoImplicit false

/-!
# 第十章　散乱解・散乱行列の存在、一意性、およびユニタリティ

## 対象と仮定

第一〜第九章と同じ有限内部格子 Grid N、自由質量二乗行列M₀²、
第八章の自己共役な区分定数障壁 BarrierLayer の有限リストを扱う。
障壁幅は各層で厳密に正であり、空リストも許す。
外部ではポテンシャルがゼロで、左右で同じ外部チャネル基底を使う。

周波数と横方向運動量を固定し、次の条件を要求する。

    AllExteriorChannelsOpen p s k
    Ω²I - M₀² > 0、すなわち全外部チャネルの波数kα > 0

閾値kα=0や、閉じた外部チャネルを含む問題は本章の対象に含めない。
障壁内部で全チャネルが開いていることや、内部の係数行列の正定値性は要求しない。
散乱解の存在、一意性、散乱行列の存在、ユニタリティを仮定には置かない。

## 構成と証明の順序

1. 第九章の流束保存を、入射振幅ゼロの境界方程式に適用する。
   出射流束の正値性から、出射振幅を未知数とする正方線形写像の核がゼロとなる。
   有限次元での可逆性を用い、入射振幅aから出射振幅bへの線形写像と行列Sを構成する。
2. 外部の平面波と各層の行列指数解を実際に接続し、全実数上の関数y=(f,f')を作る。
   接続点ではyの連続性を証明し、それ以外では第八章の微分方程式を証明する。
   従って、端点の有限次元条件の可解性だけで存在の証明を済ませない。
3. 任意の散乱解から端点条件を回収する。各層内の微分方程式の一意性を証明し、
   出射振幅と全域関数yの組が、任意の入射振幅に対して一意に存在することを示す。
4. 任意の複素入射振幅に対する流束保存から、重み付き行列恒等式と、
   流束規格化後の通常のユニタリティを導く。

左右の入出射規約は第八・第九章から引き継ぐ。

    a = (aL,aR)、b = (bL,bR)、b = S a
    K = diag(kα)、W = diag(K^(1/2),K^(1/2))
    SF = W S W⁻¹
    S† W² S = W²
    SF† SF = I、SF SF† = I

未規格化のSについては重み付き内積の保存を示す。
正定値内積に関するユニタリティは、具体的に定義したSFについて証明する。
列ごとの確率総和だけでなく、任意の重ね合わせの流束保存を使い、列の直交性も得る。

## 主要定理

* scatteringMatrix_exists_unique：境界条件を満たす散乱行列の存在・一意性。
* assembledScatteringState_solves：構成した全域関数がIsScatteringSolutionを満たす。
* boundaryMatching_iff_solution_exists：端点条件と全域散乱解の存在の同値性。
* scattering_solution_exists_unique：任意の入射振幅に対する出射振幅・全域解の存在・一意性。
* scatteringMatrix_exists_unique_for_solutions：実際の散乱解を与える行列の存在・一意性。
* scatteringMatrix_weighted_unitary：未規格化の散乱行列の重み付き保存式。
* fluxNormalizedScatteringMatrix_unitary：規格化した行列の両側のユニタリティ。

これらは有限チャネルの静的な線形波動散乱についての定理である。
量子場理論の相互作用S行列、時間依存障壁、一般の連続ポテンシャルへの拡張は扱わない。
第七章の安定性の仮定を除去する主張や、三時間を物理的時計と同定する主張も含めない。

## 利用方法と検証環境

第一〜第九章を同じmathlibプロジェクト内に配置し、先行章をコンパイルしてから：

    lake env lean -DwarningAsError=true Chapter10_ScatteringUnitarity.lean

Lean 4.24.0 / mathlib v4.24.0。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
存在の構成は数学的な非計算的定義を含む。数値散乱計算の実装ではない。
末尾の #print axioms で主要定理の公理依存を確認する。
-/

noncomputable section
open scoped BigOperators ComplexOrder Topology
open Set Filter
namespace TwelveDimensionalPhaseSpace
namespace ScatteringUnitarity
/-! ## 10.1　流束保存から境界方程式の可逆性と散乱行列を構成する -/

section BoundaryAlgebra
open StaticScattering WronskianFlux

variable {N : ℕ} [NeZero N]

def phaseMatrix (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    InternalMatrix N := Matrix.diagonal (fun α => phaseRate (channelWaveNumber p s k α))

theorem exteriorProfile_zero (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (a b : InternalVector N) :
    exteriorProfile p s k a b 0 = (exteriorUnitary p s k).mulVec (a + b) := by
  rw [exteriorProfile_repr]
  congr 1
  ext α
  simp [profileCoefficients, planeWave]

theorem exteriorSlope_zero (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (a b : InternalVector N) :
    exteriorSlope p s k a b 0 =
      (exteriorUnitary p s k * phaseMatrix p s k).mulVec (a - b) := by
  rw [exteriorSlope_repr, ← Matrix.mulVec_mulVec]
  congr 1
  ext α
  simp [slopeCoefficients, phaseMatrix, planeWave, phaseRate, Matrix.mulVec_diagonal]
  ring

def leftIncomingMatrix (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    ScatteringMatrix N :=
  Matrix.fromBlocks (exteriorUnitary p s k) 0 (exteriorUnitary p s k * phaseMatrix p s k) 0

def leftOutgoingMatrix (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    ScatteringMatrix N :=
  Matrix.fromBlocks (exteriorUnitary p s k) 0 (-(exteriorUnitary p s k * phaseMatrix p s k)) 0

def rightIncomingMatrix (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    ScatteringMatrix N :=
  Matrix.fromBlocks 0 (exteriorUnitary p s k) 0 (-(exteriorUnitary p s k * phaseMatrix p s k))

def rightOutgoingMatrix (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    ScatteringMatrix N :=
  Matrix.fromBlocks 0 (exteriorUnitary p s k) 0 (exteriorUnitary p s k * phaseMatrix p s k)

theorem leftBoundary_linear (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (a b : StateVector N) :
    leftExteriorState p s k ⟨a, b⟩ 0 =
      (leftIncomingMatrix p s k).mulVec a + (leftOutgoingMatrix p s k).mulVec b := by
  unfold leftExteriorState
  rw [exteriorProfile_zero, exteriorSlope_zero]
  ext (n | n) <;> simp [leftIncomingMatrix, leftOutgoingMatrix, Matrix.fromBlocks_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.neg_mulVec, sub_eq_add_neg,
    packState, Function.comp_def]

theorem rightBoundary_linear (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (width : ℝ) (a b : StateVector N) :
    rightExteriorState p s k width ⟨a, b⟩ width =
      (rightIncomingMatrix p s k).mulVec a + (rightOutgoingMatrix p s k).mulVec b := by
  simp only [rightExteriorState, sub_self]
  rw [exteriorProfile_zero, exteriorSlope_zero]
  ext (n | n) <;> simp [rightIncomingMatrix, rightOutgoingMatrix, Matrix.fromBlocks_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.neg_mulVec, sub_eq_add_neg,
    packState, Function.comp_def, add_comm]

def outgoingOperator (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) : StateVector N →ₗ[ℂ] StateVector N :=
  (totalTransfer p s k layers * leftOutgoingMatrix p s k - rightOutgoingMatrix p s k).toLin'

def incomingOperator (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) : StateVector N →ₗ[ℂ] StateVector N :=
  (rightIncomingMatrix p s k - totalTransfer p s k layers * leftIncomingMatrix p s k).toLin'

theorem boundaryMatching_iff_operator (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (a b : StateVector N) :
    BoundaryMatching p s k layers ⟨a, b⟩ ↔
      outgoingOperator p s k layers b = incomingOperator p s k layers a := by
  unfold BoundaryMatching
  rw [leftBoundary_linear, rightBoundary_linear, Matrix.mulVec_add]
  simp only [outgoingOperator, incomingOperator, Matrix.toLin'_apply, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec]
  rw [sub_eq_sub_iff_add_eq_add]
  constructor <;> intro h <;> simpa only [add_comm] using h

theorem outgoingOperator_kernel_zero (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (b : StateVector N)
    (hb : outgoingOperator p s k layers b = 0) : b = 0 := by
  have hm : BoundaryMatching p s k layers ⟨0, b⟩ :=
    (boundaryMatching_iff_operator p s k layers 0 b).mpr (by simpa only [map_zero] using hb)
  have hf := boundaryMatching_fluxBalance p s k layers ⟨0, b⟩ hm
  have he : weightedNorm p s k (fun α => b (Sum.inl α)) +
      weightedNorm p s k (fun α => b (Sum.inr α)) = 0 := by
    simpa [incomingFlux, outgoingFlux, weightedNorm] using hf.symm
  have hl := weightedNorm_nonneg p s k hOpen (fun α => b (Sum.inl α))
  have hr := weightedNorm_nonneg p s k hOpen (fun α => b (Sum.inr α))
  have hl0 : weightedNorm p s k (fun α => b (Sum.inl α)) = 0 := by linarith
  have hr0 : weightedNorm p s k (fun α => b (Sum.inr α)) = 0 := by linarith
  have hleft := (weightedNorm_eq_zero_iff p s k hOpen _).mp hl0
  have hright := (weightedNorm_eq_zero_iff p s k hOpen _).mp hr0
  funext c
  cases c with
  | inl α => exact congrFun hleft α
  | inr α => exact congrFun hright α

theorem outgoingOperator_injective (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) :
    Function.Injective (outgoingOperator p s k layers) := by
  intro b c hbc
  have hz : outgoingOperator p s k layers (b - c) = 0 := by rw [map_sub, hbc, sub_self]
  exact sub_eq_zero.mp (outgoingOperator_kernel_zero p s k layers hOpen (b - c) hz)

def outgoingEquiv (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (hOpen : AllExteriorChannelsOpen p s k) :
    StateVector N ≃ₗ[ℂ] StateVector N :=
  LinearEquiv.ofInjectiveEndo (outgoingOperator p s k layers)
    (outgoingOperator_injective p s k layers hOpen)

def scatteringLinearMap (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (hOpen : AllExteriorChannelsOpen p s k) :
    StateVector N →ₗ[ℂ] StateVector N :=
  (outgoingEquiv p s k layers hOpen).symm.toLinearMap.comp (incomingOperator p s k layers)

theorem scatteringLinearMap_matches (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a : StateVector N) :
    BoundaryMatching p s k layers ⟨a, scatteringLinearMap p s k layers hOpen a⟩ := by
  apply (boundaryMatching_iff_operator p s k layers _ _).mpr
  change outgoingEquiv p s k layers hOpen
    ((outgoingEquiv p s k layers hOpen).symm (incomingOperator p s k layers a)) = _
  exact (outgoingEquiv p s k layers hOpen).apply_symm_apply _

theorem scatteringLinearMap_unique (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a b : StateVector N)
    (hb : BoundaryMatching p s k layers ⟨a, b⟩) :
    b = scatteringLinearMap p s k layers hOpen a := by
  have he := (boundaryMatching_iff_operator p s k layers a b).mp hb
  apply (outgoingEquiv p s k layers hOpen).injective
  change outgoingOperator p s k layers b = outgoingOperator p s k layers
    (scatteringLinearMap p s k layers hOpen a)
  rw [he]
  exact ((boundaryMatching_iff_operator p s k layers _ _).mp
    (scatteringLinearMap_matches p s k layers hOpen a)).symm

def scatteringMatrix (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (hOpen : AllExteriorChannelsOpen p s k) : ScatteringMatrix N :=
  LinearMap.toMatrix' (scatteringLinearMap p s k layers hOpen)

theorem scatteringMatrix_mulVec (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a : StateVector N) :
    (scatteringMatrix p s k layers hOpen).mulVec a = scatteringLinearMap p s k layers hOpen a :=
  LinearMap.toMatrix'_mulVec _ a

theorem scatteringMatrix_matches (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a : StateVector N) :
    BoundaryMatching p s k layers ⟨a, (scatteringMatrix p s k layers hOpen).mulVec a⟩ := by
  rw [scatteringMatrix_mulVec]
  exact scatteringLinearMap_matches p s k layers hOpen a

theorem scatteringMatrix_exists_unique (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) :
    ∃! S : ScatteringMatrix N, ∀ a : StateVector N, BoundaryMatching p s k layers ⟨a, S.mulVec a⟩ := by
  refine ⟨scatteringMatrix p s k layers hOpen, scatteringMatrix_matches p s k layers hOpen, ?_⟩
  intro R hR
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro a
  simpa only [Matrix.toLin'_apply, scatteringMatrix_mulVec] using
    scatteringLinearMap_unique p s k layers hOpen a (R.mulVec a) (hR a)

def channelNorm (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (a : StateVector N) : ℝ :=
  weightedNorm p s k (fun α => a (Sum.inl α)) + weightedNorm p s k (fun α => a (Sum.inr α))

theorem scatteringMatrix_preserves_channelNorm (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a : StateVector N) :
    channelNorm p s k ((scatteringMatrix p s k layers hOpen).mulVec a) = channelNorm p s k a :=
  (boundaryMatching_fluxBalance p s k layers _ (scatteringMatrix_matches p s k layers hOpen a)).symm


end BoundaryAlgebra
open StaticScattering WronskianFlux

/-! ## 10.2　層ごとの解析解、接続、および全域解の一意性

定数係数の微分方程式について、閉区間上の連続性と開区間上の微分方程式から
行列指数解との一致を導く。接続点で微分可能であるという追加仮定は置かない。
-/

section LocalUniqueness
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integratingFactor_point (B : Matrix ι ι ℂ) (y : ℝ → ι → ℂ) (x : ℝ)
    (hy : HasDerivAt y (B.mulVec (y x)) x) :
    HasDerivAt (fun t => (NormedSpace.exp ℝ (t • (-matrixGenerator B))) (y t)) 0 x := by
  have hd := (hasDerivAt_exp_smul_const (-matrixGenerator B) x).clm_apply hy
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
    matrixGenerator_apply, map_neg, neg_add_cancel] using hd

theorem matrixFlow_uniqueOn (B : Matrix ι ι ℂ) (y : ℝ → ι → ℂ) (hy : Continuous y)
    (width : ℝ) (hODE : ∀ t ∈ Ioo 0 width, HasDerivAt y (B.mulVec (y t)) t)
    (x : ℝ) (hx : x ∈ Icc 0 width) : y x = matrixFlow B (y 0) x := by
  let F : ℝ → ι → ℂ := fun t =>
    (NormedSpace.exp ℝ (t • (-matrixGenerator B)) : (ι → ℂ) →L[ℝ] (ι → ℂ)) (y t)
  have hExp : Continuous (fun t : ℝ =>
      (NormedSpace.exp ℝ (t • (-matrixGenerator B)) : (ι → ℂ) →L[ℝ] (ι → ℂ))) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_exp_smul_const (-matrixGenerator B) t).continuousAt)
  have hF : Continuous F := hExp.clm_apply hy
  have hFD (t : ℝ) (ht : t ∈ Ioo 0 x) : HasDerivAt F 0 t :=
    integratingFactor_point B y t (hODE t ⟨ht.1, lt_of_lt_of_le ht.2 hx.2⟩)
  have hconst : F x = F 0 := by
    funext i
    apply Complex.ext
    · apply Eq.symm
      apply real_constant_interval (fun t => (F t i).re)
        (Complex.continuous_re.comp ((continuous_apply i).comp hF)) 0 x hx.1
      intro t ht
      have hc := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i).hasFDerivAt.comp_hasDerivAt t (hFD t ht)
      simpa using Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc
    · apply Eq.symm
      apply real_constant_interval (fun t => (F t i).im)
        (Complex.continuous_im.comp ((continuous_apply i).comp hF)) 0 x hx.1
      intro t ht
      have hc := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i).hasFDerivAt.comp_hasDerivAt t (hFD t ht)
      simpa using Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hc
  have hFzero : F 0 = y 0 := by
    have hs : (0 : ℝ) • (-matrixGenerator B) = 0 := by
      ext z i
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply,
        Pi.smul_apply, Pi.zero_apply, zero_smul]
    have hz : (NormedSpace.exp ℝ (0 : (ι → ℂ) →L[ℝ] (ι → ℂ))) = 1 := NormedSpace.exp_zero
    have he := (congrArg (fun T : (ι → ℂ) →L[ℝ] (ι → ℂ) => NormedSpace.exp ℝ T) hs).trans hz
    exact congrArg (fun T : (ι → ℂ) →L[ℝ] (ι → ℂ) => T (y 0)) he
  have hconst' :
      (NormedSpace.exp ℝ (x • (-matrixGenerator B)) : (ι → ℂ) →L[ℝ] (ι → ℂ)) (y x) = y 0 :=
    hconst.trans hFzero
  have he := congrArg (fun z : ι → ℂ =>
    (NormedSpace.exp ℝ (x • matrixGenerator B) : (ι → ℂ) →L[ℝ] (ι → ℂ)) z) hconst'
  have hi : NormedSpace.exp ℝ (x • matrixGenerator B) *
      NormedSpace.exp ℝ (x • (-matrixGenerator B)) = 1 := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl (x • matrixGenerator B)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  have hApplied := congrArg (fun T : (ι → ℂ) →L[ℝ] (ι → ℂ) => T (y x)) hi
  exact hApplied.symm.trans he

omit [DecidableEq ι] in
theorem finitePi_hasDerivAt {f : ℝ → ι → ℂ} {f' : ι → ℂ} {x : ℝ}
    (h : ∀ i, HasDerivAt (fun t => f t i) (f' i) x) : HasDerivAt f f' x := by
  have hd := hasFDerivAt_pi.mpr (fun i => (h i).hasFDerivAt)
  simpa using hd.hasDerivAt

end LocalUniqueness

/-! ### 外部平面波も同じ一階連立方程式を満たす -/

section ExteriorAnalysis
variable {N : ℕ} [NeZero N]

def freeExteriorCoefficient (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) : InternalMatrix N :=
  freeMassSquared p s - realScalarMatrix (reducedFrequencySquared k)

theorem freeExterior_eigenvector (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hOpen : AllExteriorChannelsOpen p s k) (α : Grid N) :
    (freeExteriorCoefficient p s k).mulVec ⇑(exteriorBasis p s k α) =
      (-((channelWaveNumber p s k α ^ 2 : ℝ) : ℂ)) • ⇑(exteriorBasis p s k α) := by
  rw [freeExteriorCoefficient, Matrix.sub_mulVec, exteriorBasis_massEigenvector,
    realScalarMatrix, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext n
  simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [channelWaveNumber_sq p s k hOpen α]
  push_cast
  ring

theorem freeExterior_action (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hOpen : AllExteriorChannelsOpen p s k) (c : InternalVector N) :
    (freeExteriorCoefficient p s k).mulVec ((exteriorUnitary p s k).mulVec c) =
      (exteriorUnitary p s k).mulVec
        (fun α => -((channelWaveNumber p s k α ^ 2 : ℝ) : ℂ) * c α) := by
  let D : InternalMatrix N := Matrix.diagonal (fun α => -((channelWaveNumber p s k α ^ 2 : ℝ) : ℂ))
  have hm : freeExteriorCoefficient p s k * exteriorUnitary p s k = exteriorUnitary p s k * D := by
    ext n α
    rw [Matrix.mul_diagonal]
    change ((freeExteriorCoefficient p s k).mulVec ⇑(exteriorBasis p s k α)) n =
      (exteriorBasis p s k α) n * -((channelWaveNumber p s k α ^ 2 : ℝ) : ℂ)
    rw [freeExterior_eigenvector p s k hOpen α]
    exact mul_comm _ _
  rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec]
  have hDc : D.mulVec c = fun α => -((channelWaveNumber p s k α ^ 2 : ℝ) : ℂ) * c α := by
    ext α
    simp only [D, Matrix.mulVec_diagonal]
  exact congrArg (fun v => (exteriorUnitary p s k).mulVec v) hDc

theorem planeSlope_hasDerivAt (κ : ℝ) (a : ℂ) (x : ℝ) :
    HasDerivAt (fun t => phaseRate κ * planeWave κ t * a)
      (-((κ ^ 2 : ℝ) : ℂ) * planeWave κ x * a) x := by
  have hd := ((planeWave_hasDerivAt κ x).const_mul (phaseRate κ)).mul_const a
  have he : phaseRate κ * (phaseRate κ * planeWave κ x) * a =
      -((κ ^ 2 : ℝ) : ℂ) * planeWave κ x * a := by
    calc
      _ = phaseRate κ ^ 2 * planeWave κ x * a := by ring
      _ = _ := by rw [phaseRate_sq]
  rw [he] at hd
  exact hd

theorem profileCoefficients_hasDerivAt (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (a b : InternalVector N) (x : ℝ) :
    HasDerivAt (profileCoefficients p s k a b) (slopeCoefficients p s k a b x) x := by
  apply finitePi_hasDerivAt
  intro α
  exact ((planeWave_hasDerivAt (channelWaveNumber p s k α) x).mul_const (a α)).add
    ((planeWave_hasDerivAt (-channelWaveNumber p s k α) x).mul_const (b α))

theorem slopeCoefficients_hasDerivAt (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (a b : InternalVector N) (x : ℝ) :
    HasDerivAt (slopeCoefficients p s k a b)
      (fun α => -((channelWaveNumber p s k α ^ 2 : ℝ) : ℂ) *
        profileCoefficients p s k a b x α) x := by
  apply finitePi_hasDerivAt
  intro α
  have hd := (planeSlope_hasDerivAt (channelWaveNumber p s k α) (a α) x).add
    (planeSlope_hasDerivAt (-channelWaveNumber p s k α) (b α) x)
  simpa only [slopeCoefficients, profileCoefficients, neg_sq, mul_add, mul_assoc] using hd

def exteriorState (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (a b : InternalVector N) (x : ℝ) : StateVector N :=
  packState (exteriorProfile p s k a b x) (exteriorSlope p s k a b x)

theorem exteriorState_hasDerivAt (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hOpen : AllExteriorChannelsOpen p s k)
    (a b : InternalVector N) (x : ℝ) :
    HasDerivAt (exteriorState p s k a b)
      ((stationaryGenerator (freeExteriorCoefficient p s k)).mulVec (exteriorState p s k a b x)) x := by
  have hc := profileCoefficients_hasDerivAt p s k a b x
  have hd := slopeCoefficients_hasDerivAt p s k a b x
  have hp : exteriorProfile p s k a b = fun t =>
      (exteriorUnitary p s k).mulVec (profileCoefficients p s k a b t) :=
    funext (fun t => exteriorProfile_repr p s k a b t)
  have hs : exteriorSlope p s k a b = fun t =>
      (exteriorUnitary p s k).mulVec (slopeCoefficients p s k a b t) :=
    funext (fun t => exteriorSlope_repr p s k a b t)
  have hf : HasDerivAt (exteriorProfile p s k a b) (exteriorSlope p s k a b x) x := by
    rw [hp, exteriorSlope_repr]
    exact (matrixGenerator (exteriorUnitary p s k)).hasFDerivAt.comp_hasDerivAt x hc
  have hg : HasDerivAt (exteriorSlope p s k a b)
      ((freeExteriorCoefficient p s k).mulVec (exteriorProfile p s k a b x)) x := by
    rw [hs, exteriorProfile_repr, freeExterior_action p s k hOpen]
    exact (matrixGenerator (exteriorUnitary p s k)).hasFDerivAt.comp_hasDerivAt x hd
  rw [stationaryGenerator_action]
  apply finitePi_hasDerivAt
  intro j
  cases j with
  | inl n => exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Grid N => ℂ) n).hasFDerivAt.comp_hasDerivAt x hf
  | inr n => exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Grid N => ℂ) n).hasFDerivAt.comp_hasDerivAt x hg

theorem leftExterior_hasDerivAt (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hOpen : AllExteriorChannelsOpen p s k)
    (a : ExteriorAmplitudes N) (x : ℝ) :
    HasDerivAt (leftExteriorState p s k a)
      ((stationaryGenerator (freeExteriorCoefficient p s k)).mulVec (leftExteriorState p s k a x)) x :=
  exteriorState_hasDerivAt p s k hOpen _ _ x

theorem rightExterior_hasDerivAt (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hOpen : AllExteriorChannelsOpen p s k)
    (width : ℝ) (a : ExteriorAmplitudes N) (x : ℝ) :
    HasDerivAt (rightExteriorState p s k width a)
      ((stationaryGenerator (freeExteriorCoefficient p s k)).mulVec (rightExteriorState p s k width a x)) x := by
  have hd := (exteriorState_hasDerivAt p s k hOpen
    (fun α => a.outgoing (Sum.inr α)) (fun α => a.incoming (Sum.inr α)) (x - width)).scomp x
      ((hasDerivAt_id x).sub_const width)
  simpa only [one_smul] using hd

end ExteriorAnalysis

/-! ### 有限個の層を接続する関数の構成 -/

section LayerGluing
variable {N : ℕ} [NeZero N]

def coefficientAt (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (x : ℝ) : InternalMatrix N :=
  freeMassSquared p s + layeredPotential layers x - realScalarMatrix (reducedFrequencySquared k)

theorem interfaces_zero (layers : List (BarrierLayer N)) : (0 : ℝ) ∈ interfaces layers := by
  cases layers <;> simp [interfaces]

theorem interfaces_width (l : BarrierLayer N) (rest : List (BarrierLayer N)) :
    l.width ∈ interfaces (l :: rest) := by
  apply List.mem_cons_of_mem
  exact List.mem_map.mpr ⟨0, interfaces_zero rest, add_zero _⟩

theorem interfaces_nonneg (layers : List (BarrierLayer N)) (x : ℝ)
    (hx : x ∈ interfaces layers) : 0 ≤ x := by
  induction layers generalizing x with
  | nil =>
    have he : x = 0 := by simpa only [interfaces, List.mem_singleton] using hx
    rw [he]
  | cons l rest ih =>
    rcases List.mem_cons.mp hx with he | hm
    · simpa only [he] using (le_rfl : (0 : ℝ) ≤ 0)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
      exact add_nonneg l.width_pos.le (ih r hr)

theorem interfaces_not_first (l : BarrierLayer N) (rest : List (BarrierLayer N))
    (x : ℝ) (hx : 0 < x) (hwidth : x < l.width) : x ∉ interfaces (l :: rest) := by
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · linarith
  · obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
    have h0 := interfaces_nonneg rest r hr
    linarith

theorem interfaces_not_sub (l : BarrierLayer N) (rest : List (BarrierLayer N)) (x : ℝ)
    (hx : x ∉ interfaces (l :: rest)) : x - l.width ∉ interfaces rest := by
  intro hm
  apply hx
  apply List.mem_cons_of_mem
  exact List.mem_map.mpr ⟨x - l.width, hm, by ring⟩

theorem interfaces_not_add (l : BarrierLayer N) (rest : List (BarrierLayer N)) (x : ℝ)
    (hx : 0 < x) (hnot : x ∉ interfaces rest) : x + l.width ∉ interfaces (l :: rest) := by
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · have hw := l.width_pos
    linarith
  · obtain ⟨r, hr, he⟩ := List.mem_map.mp hm
    have her : r = x := by linarith
    exact hnot (her ▸ hr)

theorem coefficientAt_first (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (l : BarrierLayer N) (rest : List (BarrierLayer N)) (x : ℝ)
    (hx : 0 < x) (hwidth : x < l.width) :
    coefficientAt p s k (l :: rest) x = layerCoefficient p s k l := by
  simp only [coefficientAt, layeredPotential, if_neg (not_lt.mpr hx.le), if_pos hwidth, layerCoefficient]

theorem coefficientAt_rest (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (l : BarrierLayer N) (rest : List (BarrierLayer N)) (x : ℝ) (hx : l.width ≤ x) :
    coefficientAt p s k (l :: rest) x = coefficientAt p s k rest (x - l.width) := by
  have h0 : ¬ x < 0 := not_lt.mpr (le_trans l.width_pos.le hx)
  simp only [coefficientAt, layeredPotential, if_neg h0, if_neg (not_lt.mpr hx)]

theorem matrixFlow_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (y0 : ι → ℂ) : Continuous (matrixFlow B y0) :=
  continuous_iff_continuousAt.mpr (fun x => (matrixFlow_hasDerivAt B y0 x).continuousAt)

def tailState (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (a : ExteriorAmplitudes N) : List (BarrierLayer N) → StateVector N → ℝ → StateVector N
  | [], _, x => rightExteriorState p s k 0 a x
  | l :: rest, y0, x =>
      if l.width ≤ x then
        tailState p s k a rest
          (matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0 l.width) (x - l.width)
      else matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0 x

theorem tailState_zero (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (a : ExteriorAmplitudes N) (layers : List (BarrierLayer N)) (y0 : StateVector N)
    (h : propagateLayers p s k layers y0 = rightExteriorState p s k 0 a 0) :
    tailState p s k a layers y0 0 = y0 := by
  cases layers with
  | nil => exact h.symm
  | cons l rest => simp only [tailState, if_neg (not_le.mpr l.width_pos), matrixFlow_zero]

theorem tailState_continuous (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (hOpen : AllExteriorChannelsOpen p s k) (a : ExteriorAmplitudes N)
    (layers : List (BarrierLayer N)) (y0 : StateVector N)
    (h : propagateLayers p s k layers y0 = rightExteriorState p s k 0 a 0) :
    Continuous (tailState p s k a layers y0) := by
  induction layers generalizing y0 with
  | nil => exact continuous_iff_continuousAt.mpr (fun x =>
      (rightExterior_hasDerivAt p s k hOpen 0 a x).continuousAt)
  | cons l rest ih =>
    let yMid := matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0 l.width
    have hrest : propagateLayers p s k rest yMid = rightExteriorState p s k 0 a 0 := h
    have hc := ih yMid hrest
    change Continuous (fun x => if l.width ≤ x then
      tailState p s k a rest yMid (x - l.width)
      else matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0 x)
    apply Continuous.if_le (hc.comp (continuous_id.sub continuous_const))
      (matrixFlow_continuous _ _) continuous_const continuous_id
    intro x he
    change l.width = x at he
    simp only [Function.comp_apply, id_eq]
    rw [← he, sub_self, tailState_zero p s k a rest yMid hrest]

theorem rightExterior_shift (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (width shift : ℝ) (a : ExteriorAmplitudes N) (x : ℝ) :
    rightExteriorState p s k width a (x - shift) =
      rightExteriorState p s k (shift + width) a x := by
  simp only [rightExteriorState, sub_sub]

theorem tailState_right (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (a : ExteriorAmplitudes N) (layers : List (BarrierLayer N)) (y0 : StateVector N)
    (x : ℝ) (hx : totalWidth layers ≤ x) :
    tailState p s k a layers y0 x = rightExteriorState p s k (totalWidth layers) a x := by
  induction layers generalizing y0 x with
  | nil => rfl
  | cons l rest ih =>
    have hr := totalWidth_nonneg rest
    change l.width + totalWidth rest ≤ x at hx
    have hwx : l.width ≤ x := by linarith
    rw [tailState, if_pos hwx, ih _ (x - l.width) (by linarith)]
    exact rightExterior_shift p s k _ _ a x

theorem tailState_hasDerivAt (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (hOpen : AllExteriorChannelsOpen p s k) (a : ExteriorAmplitudes N)
    (layers : List (BarrierLayer N)) (y0 : StateVector N) (x : ℝ)
    (hx : 0 < x) (hnot : x ∉ interfaces layers) :
    HasDerivAt (tailState p s k a layers y0)
      ((stationaryGenerator (coefficientAt p s k layers x)).mulVec (tailState p s k a layers y0 x)) x := by
  induction layers generalizing y0 x with
  | nil => simpa only [tailState, coefficientAt, layeredPotential, add_zero, freeExteriorCoefficient] using
      rightExterior_hasDerivAt p s k hOpen 0 a x
  | cons l rest ih =>
    by_cases hwx : l.width ≤ x
    · have hne : x ≠ l.width := by intro he; exact hnot (he ▸ interfaces_width l rest)
      have hgt : l.width < x := lt_of_le_of_ne hwx hne.symm
      let yMid := matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0 l.width
      have hrest := ih yMid (x - l.width) (by linarith) (interfaces_not_sub l rest x hnot)
      have hd := hrest.scomp x ((hasDerivAt_id x).sub_const l.width)
      have heq : tailState p s k a (l :: rest) y0 =ᶠ[𝓝 x]
          (fun r => tailState p s k a rest yMid (r - l.width)) := by
        filter_upwards [Ioi_mem_nhds hgt] with r hr
        exact if_pos hr.le
      have hpoint : tailState p s k a (l :: rest) y0 x =
          tailState p s k a rest yMid (x - l.width) := if_pos hwx
      rw [coefficientAt_rest p s k l rest x hwx, hpoint]
      simpa only [one_smul] using hd.congr_of_eventuallyEq heq
    · have hlt : x < l.width := lt_of_not_ge hwx
      have heq : tailState p s k a (l :: rest) y0 =ᶠ[𝓝 x]
          matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0 := by
        filter_upwards [Iio_mem_nhds hlt] with r hr
        exact if_neg (not_le.mpr hr)
      have hpoint : tailState p s k a (l :: rest) y0 x =
          matrixFlow (stationaryGenerator (layerCoefficient p s k l)) y0 x := if_neg hwx
      rw [coefficientAt_first p s k l rest x hx hlt, hpoint]
      exact (matrixFlow_hasDerivAt _ _ x).congr_of_eventuallyEq heq

end LayerGluing

/-! ### 境界条件から第八章の全実数上の散乱解を構成する -/

section GlobalExistence
variable {N : ℕ} [NeZero N]

theorem matching_tail_condition (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N) (h : BoundaryMatching p s k layers a) :
    propagateLayers p s k layers (leftExteriorState p s k a 0) = rightExteriorState p s k 0 a 0 := by
  have he := h
  rw [BoundaryMatching, totalTransfer_action] at he
  simpa only [rightExteriorState, sub_self] using he

def assembledScatteringState (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N) (x : ℝ) : StateVector N :=
  if x ≤ 0 then leftExteriorState p s k a x
  else tailState p s k a layers (leftExteriorState p s k a 0) x

theorem assembledScatteringState_solves (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hOpen : AllExteriorChannelsOpen p s k)
    (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N)
    (hMatch : BoundaryMatching p s k layers a) :
    IsScatteringSolution p s k layers a (assembledScatteringState p s k layers a) := by
  let y0 := leftExteriorState p s k a 0
  have hcond := matching_tail_condition p s k layers a hMatch
  have hleft : Continuous (leftExteriorState p s k a) :=
    continuous_iff_continuousAt.mpr (fun x => (leftExterior_hasDerivAt p s k hOpen a x).continuousAt)
  have htail := tailState_continuous p s k hOpen a layers y0 hcond
  have hc : Continuous (assembledScatteringState p s k layers a) := by
    change Continuous (fun x => if x ≤ 0 then leftExteriorState p s k a x
      else tailState p s k a layers y0 x)
    apply Continuous.if_le hleft htail continuous_id continuous_const
    intro x hx
    change x = 0 at hx
    subst x
    exact (tailState_zero p s k a layers y0 hcond).symm
  refine ⟨hc, ?_, ?_, ?_⟩
  · intro x hx
    change HasDerivAt (assembledScatteringState p s k layers a)
      ((stationaryGenerator (coefficientAt p s k layers x)).mulVec
        (assembledScatteringState p s k layers a x)) x
    by_cases hneg : x ≤ 0
    · have hne : x ≠ 0 := by intro he; subst x; exact hx (interfaces_zero layers)
      have hlt : x < 0 := lt_of_le_of_ne hneg hne
      have heq : assembledScatteringState p s k layers a =ᶠ[𝓝 x] leftExteriorState p s k a := by
        filter_upwards [Iio_mem_nhds hlt] with r hr
        exact if_pos hr.le
      have hpoint : assembledScatteringState p s k layers a x = leftExteriorState p s k a x := if_pos hneg
      have hcoef : coefficientAt p s k layers x = freeExteriorCoefficient p s k := by
        simp only [coefficientAt, layeredPotential_left_zero layers x hlt, add_zero, freeExteriorCoefficient]
      rw [hcoef, hpoint]
      exact (leftExterior_hasDerivAt p s k hOpen a x).congr_of_eventuallyEq heq
    · have hpos : 0 < x := lt_of_not_ge hneg
      have heq : assembledScatteringState p s k layers a =ᶠ[𝓝 x]
          tailState p s k a layers y0 := by
        filter_upwards [Ioi_mem_nhds hpos] with r hr
        exact if_neg (not_le.mpr hr)
      have hpoint : assembledScatteringState p s k layers a x = tailState p s k a layers y0 x := if_neg hneg
      rw [hpoint]
      exact (tailState_hasDerivAt p s k hOpen a layers y0 x hpos hx).congr_of_eventuallyEq heq
  · intro x hx
    exact if_pos hx
  · intro x hx
    by_cases hneg : x ≤ 0
    · have he : x = 0 := le_antisymm hneg (le_trans (totalWidth_nonneg layers) hx)
      subst x
      rw [assembledScatteringState, if_pos le_rfl]
      exact (tailState_zero p s k a layers y0 hcond).symm.trans
        (tailState_right p s k a layers y0 0 hx)
    · rw [assembledScatteringState, if_neg hneg]
      exact tailState_right p s k a layers y0 x hx

end GlobalExistence

/-! ### 任意の散乱解から境界条件を回収し、全域での一意性を示す -/

section InteriorUniqueness
variable {N : ℕ} [NeZero N]

def IsInteriorSolution (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (y : ℝ → StateVector N) : Prop :=
  Continuous y ∧ ∀ x, 0 < x → x < totalWidth layers → x ∉ interfaces layers →
    HasDerivAt y ((stationaryGenerator (coefficientAt p s k layers x)).mulVec (y x)) x

theorem scattering_to_interior (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N) (y : ℝ → StateVector N)
    (h : IsScatteringSolution p s k layers a y) : IsInteriorSolution p s k layers y :=
  ⟨h.1, fun x _ _ hx => h.2.1 x hx⟩

theorem interior_first (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (l : BarrierLayer N) (rest : List (BarrierLayer N)) (y : ℝ → StateVector N)
    (h : IsInteriorSolution p s k (l :: rest) y) :
    ∀ x ∈ Ioo 0 l.width, HasDerivAt y
      ((stationaryGenerator (layerCoefficient p s k l)).mulVec (y x)) x := by
  intro x hx
  have htotal : x < totalWidth (l :: rest) := by
    change x < l.width + totalWidth rest
    exact lt_of_lt_of_le hx.2 (le_add_of_nonneg_right (totalWidth_nonneg rest))
  have hd := h.2 x hx.1 htotal (interfaces_not_first l rest x hx.1 hx.2)
  rw [coefficientAt_first p s k l rest x hx.1 hx.2] at hd
  exact hd

theorem interior_shift (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (l : BarrierLayer N) (rest : List (BarrierLayer N)) (y : ℝ → StateVector N)
    (h : IsInteriorSolution p s k (l :: rest) y) :
    IsInteriorSolution p s k rest (fun x => y (x + l.width)) := by
  refine ⟨h.1.comp (continuous_id.add continuous_const), ?_⟩
  intro x hx hw hnot
  have hpos : 0 < x + l.width := add_pos hx l.width_pos
  have htotal : x + l.width < totalWidth (l :: rest) := by
    change x + l.width < l.width + totalWidth rest
    linarith
  have hd := h.2 (x + l.width) hpos htotal (interfaces_not_add l rest x hx hnot)
  have hcomp := hd.scomp x ((hasDerivAt_id x).add_const l.width)
  have hcoef := coefficientAt_rest p s k l rest (x + l.width) (by linarith)
  simp only [add_sub_cancel_right] at hcoef
  rw [hcoef] at hcomp
  simpa only [one_smul] using hcomp

theorem interior_to_chain (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (y : ℝ → StateVector N)
    (h : IsInteriorSolution p s k layers y) :
    IsLayerChain p s k layers (y 0) (y (totalWidth layers)) := by
  induction layers generalizing y with
  | nil => rfl
  | cons l rest ih =>
    have hrest := ih (fun x => y (x + l.width)) (interior_shift p s k l rest y h)
    have he := matrixFlow_uniqueOn (stationaryGenerator (layerCoefficient p s k l)) y h.1 l.width
      (interior_first p s k l rest y h) l.width ⟨l.width_pos.le, le_rfl⟩
    refine ⟨matrixFlow (stationaryGenerator (layerCoefficient p s k l)) (y 0),
      matrixFlow_zero _ _, matrixFlow_hasDerivAt _ _, ?_⟩
    have hr : IsLayerChain p s k rest (y l.width) (y (l.width + totalWidth rest)) := by
      simpa only [zero_add, add_zero, add_comm] using hrest
    rw [he] at hr
    exact hr

theorem scattering_implies_matching (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N)
    (y : ℝ → StateVector N) (h : IsScatteringSolution p s k layers a y) :
    BoundaryMatching p s k layers a := by
  have hc := interior_to_chain p s k layers y (scattering_to_interior p s k layers a y h)
  have he := (layerChain_iff p s k layers (y 0) (y (totalWidth layers))).mp hc
  rw [← totalTransfer_action p s k layers (y 0)] at he
  rw [h.2.2.1 0 le_rfl, h.2.2.2 (totalWidth layers) le_rfl] at he
  exact he.symm

theorem interior_unique (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (y z : ℝ → StateVector N)
    (hy : IsInteriorSolution p s k layers y) (hz : IsInteriorSolution p s k layers z)
    (h0 : y 0 = z 0) : ∀ x ∈ Icc 0 (totalWidth layers), y x = z x := by
  induction layers generalizing y z with
  | nil =>
    intro x hx
    have he : x = 0 := le_antisymm hx.2 hx.1
    simpa only [he] using h0
  | cons l rest ih =>
    have hfirstY := interior_first p s k l rest y hy
    have hfirstZ := interior_first p s k l rest z hz
    have hEndY := matrixFlow_uniqueOn (stationaryGenerator (layerCoefficient p s k l)) y hy.1 l.width
      hfirstY l.width ⟨l.width_pos.le, le_rfl⟩
    have hEndZ := matrixFlow_uniqueOn (stationaryGenerator (layerCoefficient p s k l)) z hz.1 l.width
      hfirstZ l.width ⟨l.width_pos.le, le_rfl⟩
    have hmid : y l.width = z l.width := by rw [hEndY, hEndZ, h0]
    have hRest := ih (fun x => y (x + l.width)) (fun x => z (x + l.width))
      (interior_shift p s k l rest y hy) (interior_shift p s k l rest z hz)
      (by simpa only [zero_add] using hmid)
    intro x hx
    by_cases hw : x ≤ l.width
    · rw [matrixFlow_uniqueOn _ y hy.1 l.width hfirstY x ⟨hx.1, hw⟩,
        matrixFlow_uniqueOn _ z hz.1 l.width hfirstZ x ⟨hx.1, hw⟩, h0]
    · have hupper : x ≤ l.width + totalWidth rest := hx.2
      have hrange : x - l.width ∈ Icc 0 (totalWidth rest) := ⟨by linarith, by linarith⟩
      simpa only [sub_add_cancel] using hRest (x - l.width) hrange

theorem scattering_profile_unique (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (a : ExteriorAmplitudes N)
    (y z : ℝ → StateVector N) (hy : IsScatteringSolution p s k layers a y)
    (hz : IsScatteringSolution p s k layers a z) : y = z := by
  have h0 : y 0 = z 0 := (hy.2.2.1 0 le_rfl).trans (hz.2.2.1 0 le_rfl).symm
  have hinside := interior_unique p s k layers y z
    (scattering_to_interior p s k layers a y hy) (scattering_to_interior p s k layers a z hz) h0
  funext x
  by_cases hleft : x ≤ 0
  · exact (hy.2.2.1 x hleft).trans (hz.2.2.1 x hleft).symm
  · by_cases hright : totalWidth layers ≤ x
    · exact (hy.2.2.2 x hright).trans (hz.2.2.2 x hright).symm
    · exact hinside x ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hright).le⟩

end InteriorUniqueness


/-! ## 10.3　任意の入射振幅に対する散乱解の存在・一意性 -/

section CompleteScattering
variable {N : ℕ} [NeZero N]

/-- 境界の有限次元条件は、全実数上の散乱解の存在と同値である。 -/
theorem boundaryMatching_iff_solution_exists (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a : ExteriorAmplitudes N) :
    BoundaryMatching p s k layers a ↔
      ∃ y : ℝ → StateVector N, IsScatteringSolution p s k layers a y := by
  constructor
  · intro h
    exact ⟨assembledScatteringState p s k layers a,
      assembledScatteringState_solves p s k hOpen layers a h⟩
  · rintro ⟨y, hy⟩
    exact scattering_implies_matching p s k layers a y hy

/-- 構成した散乱行列の出射振幅を使えば、実際の散乱解が得られる。 -/
theorem scatteringMatrix_solution_exists (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a : StateVector N) :
    IsScatteringSolution p s k layers
      ⟨a, (scatteringMatrix p s k layers hOpen).mulVec a⟩
      (assembledScatteringState p s k layers
        ⟨a, (scatteringMatrix p s k layers hOpen).mulVec a⟩) :=
  assembledScatteringState_solves p s k hOpen layers _
    (scatteringMatrix_matches p s k layers hOpen a)

/-- 同じ入射振幅を持つ任意の散乱解の出射振幅は、構成した行列で決まる。 -/
theorem scattering_outgoing_unique (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a b : StateVector N)
    (y : ℝ → StateVector N) (hy : IsScatteringSolution p s k layers ⟨a, b⟩ y) :
    b = (scatteringMatrix p s k layers hOpen).mulVec a := by
  rw [scatteringMatrix_mulVec]
  exact scatteringLinearMap_unique p s k layers hOpen a b
    (scattering_implies_matching p s k layers ⟨a, b⟩ y hy)

/-- 出射振幅と全域の状態関数の組が、各入射振幅に対して一意に存在する。 -/
theorem scattering_solution_exists_unique (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a : StateVector N) :
    ∃! sol : StateVector N × (ℝ → StateVector N),
      IsScatteringSolution p s k layers ⟨a, sol.1⟩ sol.2 := by
  let b := (scatteringMatrix p s k layers hOpen).mulVec a
  let y := assembledScatteringState p s k layers ⟨a, b⟩
  have hy : IsScatteringSolution p s k layers ⟨a, b⟩ y :=
    scatteringMatrix_solution_exists p s k layers hOpen a
  refine ⟨(b, y), hy, ?_⟩
  rintro ⟨c, z⟩ hz
  have hc : c = b := scattering_outgoing_unique p s k layers hOpen a c z hz
  apply Prod.ext hc
  change z = y
  have hz' : IsScatteringSolution p s k layers ⟨a, b⟩ z := by
    simpa only [hc] using hz
  exact scattering_profile_unique p s k layers ⟨a, b⟩ z y hz' hy

/-- 全入射振幅に対して実際の散乱解を与える行列も一意である。 -/
theorem scatteringMatrix_exists_unique_for_solutions (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) :
    ∃! S : ScatteringMatrix N, ∀ a : StateVector N,
      ∃ y : ℝ → StateVector N, IsScatteringSolution p s k layers ⟨a, S.mulVec a⟩ y := by
  refine ⟨scatteringMatrix p s k layers hOpen, ?_, ?_⟩
  · intro a
    exact ⟨_, scatteringMatrix_solution_exists p s k layers hOpen a⟩
  · intro R hR
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro a
    obtain ⟨y, hy⟩ := hR a
    exact scattering_outgoing_unique p s k layers hOpen a (R.mulVec a) y hy

end CompleteScattering

/-! ## 10.4　任意の重ね合わせの流束保存から通常のユニタリティへ -/

section WeightedMatrices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def weightedSquare (w : ι → ℝ) (a : ι → ℂ) : ℝ := ∑ i, w i * Complex.normSq (a i)
def squareNorm (a : ι → ℂ) : ℝ := ∑ i, Complex.normSq (a i)

def weightRoot (w : ι → ℝ) : Matrix ι ι ℂ := Matrix.diagonal (fun i => (Real.sqrt (w i) : ℂ))
def weightRootInv (w : ι → ℝ) : Matrix ι ι ℂ := Matrix.diagonal (fun i => (Real.sqrt (w i) : ℂ)⁻¹)

theorem weightRoot_inverse (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    weightRoot w * weightRootInv w = 1 ∧ weightRootInv w * weightRoot w = 1 := by
  have hn (i : ι) : (Real.sqrt (w i) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw i)).ne'
  constructor
  · simp only [weightRoot, weightRootInv, Matrix.diagonal_mul_diagonal]
    have he : (fun i => (Real.sqrt (w i) : ℂ) * (Real.sqrt (w i) : ℂ)⁻¹) = fun _ => (1 : ℂ) :=
      funext (fun i => mul_inv_cancel₀ (hn i))
    rw [he, Matrix.diagonal_one]
  · simp only [weightRoot, weightRootInv, Matrix.diagonal_mul_diagonal]
    have he : (fun i => (Real.sqrt (w i) : ℂ)⁻¹ * (Real.sqrt (w i) : ℂ)) = fun _ => (1 : ℂ) :=
      funext (fun i => inv_mul_cancel₀ (hn i))
    rw [he, Matrix.diagonal_one]

omit [Fintype ι] in
theorem weightRoot_adjoint (w : ι → ℝ) : (weightRoot w).conjTranspose = weightRoot w := by
  simp [weightRoot]

theorem squareNorm_weightRoot (w : ι → ℝ) (hw : ∀ i, 0 < w i) (a : ι → ℂ) :
    squareNorm ((weightRoot w).mulVec a) = weightedSquare w a := by
  unfold squareNorm weightedSquare
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightRoot, Matrix.mulVec_diagonal, map_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (hw i).le]

omit [DecidableEq ι] in
theorem squareNorm_hilbert (a : ι → ℂ) :
    squareNorm a = ‖(WithLp.toLp 2 a : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [squareNorm, Complex.sq_norm]
  rfl

theorem unitary_of_squareNorm (S : Matrix ι ι ℂ)
    (hS : ∀ a, squareNorm (S.mulVec a) = squareNorm a) : IsUnitaryMatrix S := by
  have hNorm (u : EuclideanSpace ℂ ι) : ‖S.toEuclideanLin u‖ = ‖u‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have he := hS ⇑u
    rw [squareNorm_hilbert, squareNorm_hilbert] at he
    simpa only [Matrix.toEuclideanLin_apply, WithLp.toLp_ofLp] using he
  have hInner := (LinearMap.norm_map_iff_inner_map_map S.toEuclideanLin).mp hNorm
  have hPair (u v : ι → ℂ) : star (S.mulVec u) ⬝ᵥ (S.mulVec v) = star u ⬝ᵥ v := by
    have he := hInner (WithLp.toLp 2 u) (WithLp.toLp 2 v)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply,
      WithLp.ofLp_toLp, dotProduct_comm] using he
  have hStar : S.conjTranspose * S = 1 := by
    apply matrix_eq_of_form_eq
    intro u v
    calc
      form (S.conjTranspose * S) u v = form 1 (S.mulVec u) (S.mulVec v) := by
        rw [form_congruence, Matrix.mul_one]
      _ = form 1 u v := by simpa only [form, Matrix.one_mulVec] using hPair u v
  exact ⟨hStar, Matrix.mul_eq_one_comm.mp hStar⟩

def normalizedMatrix (w : ι → ℝ) (S : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  weightRoot w * S * weightRootInv w

theorem normalizedMatrix_unitary (w : ι → ℝ) (hw : ∀ i, 0 < w i) (S : Matrix ι ι ℂ)
    (hS : ∀ a, weightedSquare w (S.mulVec a) = weightedSquare w a) :
    IsUnitaryMatrix (normalizedMatrix w S) := by
  apply unitary_of_squareNorm
  intro a
  simp only [normalizedMatrix, ← Matrix.mulVec_mulVec]
  rw [squareNorm_weightRoot w hw, hS, ← squareNorm_weightRoot w hw,
    Matrix.mulVec_mulVec, (weightRoot_inverse w hw).1, Matrix.one_mulVec]

theorem weightedMatrix_identity (w : ι → ℝ) (hw : ∀ i, 0 < w i) (S : Matrix ι ι ℂ)
    (hS : ∀ a, weightedSquare w (S.mulVec a) = weightedSquare w a) :
    S.conjTranspose * (weightRoot w * weightRoot w) * S = weightRoot w * weightRoot w := by
  have hSF := (normalizedMatrix_unitary w hw S hS).1
  have hrel : normalizedMatrix w S * weightRoot w = weightRoot w * S := by
    simp only [normalizedMatrix, Matrix.mul_assoc, (weightRoot_inverse w hw).2, Matrix.mul_one]
  have hrelStar : weightRoot w * (normalizedMatrix w S).conjTranspose =
      S.conjTranspose * weightRoot w := by
    have he := congrArg Matrix.conjTranspose hrel
    simpa only [Matrix.conjTranspose_mul, weightRoot_adjoint] using he
  calc
    S.conjTranspose * (weightRoot w * weightRoot w) * S =
      (S.conjTranspose * weightRoot w) * (weightRoot w * S) := by noncomm_ring
    _ = (weightRoot w * (normalizedMatrix w S).conjTranspose) *
        (normalizedMatrix w S * weightRoot w) := by rw [← hrelStar, ← hrel]
    _ = weightRoot w * ((normalizedMatrix w S).conjTranspose * normalizedMatrix w S) *
        weightRoot w := by noncomm_ring
    _ = weightRoot w * weightRoot w := by rw [hSF, Matrix.mul_one]

end WeightedMatrices

section ModelUnitarity
variable {N : ℕ} [NeZero N]
open StaticScattering WronskianFlux

def channelWeight (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    ScatteringChannel N → ℝ := Sum.elim (channelWaveNumber p s k) (channelWaveNumber p s k)

theorem channelWeight_pos (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (hOpen : AllExteriorChannelsOpen p s k) (i : ScatteringChannel N) : 0 < channelWeight p s k i := by
  cases i with
  | inl α => exact channelWaveNumber_pos p s k hOpen α
  | inr α => exact channelWaveNumber_pos p s k hOpen α

theorem channelNorm_eq_weightedSquare (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (a : StateVector N) :
    channelNorm p s k a = weightedSquare (channelWeight p s k) a := by
  simp only [channelNorm, weightedNorm, weightedSquare, Fintype.sum_sum_type, channelWeight]
  rfl

def fluxNormalizedScatteringMatrix (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) : ScatteringMatrix N :=
  normalizedMatrix (channelWeight p s k) (scatteringMatrix p s k layers hOpen)

theorem fluxNormalizedScatteringMatrix_unitary (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) :
    IsFluxUnitary (fluxNormalizedScatteringMatrix p s k layers hOpen) := by
  apply normalizedMatrix_unitary (channelWeight p s k) (channelWeight_pos p s k hOpen)
  intro a
  simpa only [← channelNorm_eq_weightedSquare] using
    scatteringMatrix_preserves_channelNorm p s k layers hOpen a

theorem scatteringMatrix_weighted_unitary (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) :
    (scatteringMatrix p s k layers hOpen).conjTranspose *
      (weightRoot (channelWeight p s k) * weightRoot (channelWeight p s k)) *
      scatteringMatrix p s k layers hOpen =
        weightRoot (channelWeight p s k) * weightRoot (channelWeight p s k) := by
  apply weightedMatrix_identity (channelWeight p s k) (channelWeight_pos p s k hOpen)
  intro a
  simpa only [← channelNorm_eq_weightedSquare] using
    scatteringMatrix_preserves_channelNorm p s k layers hOpen a

end ModelUnitarity

/-!
## 証明範囲の確認

第八章のIsScatteringSolutionを変更せず、存在と一意性を証明した。
接続点を含む全実数上の連続性、各開区間での微分方程式、左右の外部条件をすべて満たす。
閾値・閉チャネルを除いた条件は、出射流束の正値性と規格化行列Wの可逆性に使う。

以下はLeanの公理依存の表示であり、新しい公理の宣言ではない。
-/

#print axioms outgoingOperator_kernel_zero
#print axioms scatteringMatrix_exists_unique
#print axioms matrixFlow_uniqueOn
#print axioms assembledScatteringState_solves
#print axioms scattering_implies_matching
#print axioms scattering_profile_unique
#print axioms boundaryMatching_iff_solution_exists
#print axioms scattering_solution_exists_unique
#print axioms scatteringMatrix_exists_unique_for_solutions
#print axioms scatteringMatrix_preserves_channelNorm
#print axioms unitary_of_squareNorm
#print axioms scatteringMatrix_weighted_unitary
#print axioms fluxNormalizedScatteringMatrix_unitary

end ScatteringUnitarity
end TwelveDimensionalPhaseSpace
