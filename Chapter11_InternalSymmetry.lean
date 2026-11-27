import Chapter10_ScatteringUnitarity
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

set_option autoImplicit false
/-!
# 第十一章　内部対称性・保存量・選択則

## 対象と仮定

第十章で構成した有限チャネルの静的散乱問題を扱う。
障壁は自己共役な区分定数行列の有限層であり、全外部チャネルが開いている。
第一章のSymmetryHypothesesをそのまま用い、内部行列Qについて

    Q† Q = Q Q† = I
    Q M₀² = M₀² Q
    Q V(t,x) = V(t,x) Q

を要求する。散乱行列との可換性や禁止遷移は仮定に含めない。
散乱解と散乱行列の存在・一意性は、第十章で証明した定理を用いる。

## 基底と規格化

Qは内部格子の成分基底で表した行列である。
第八章の外部固有基底Uには、縮退した固有空間内の基底の自由度がある。
従って散乱チャネルで使う対称性行列を次のように定義する。

    Qch = U† Q U
    Qtilde = diag(Qch,Qch)
    W = diag(K^(1/2),K^(1/2))、K = diag(kα)
    SF = W S W⁻¹

Qと自由質量二乗の可換性から、QchとK・K^(1/2)の可換性、
およびQtildeとWの可換性を導く。
縮退部分でQchが最初から対角であるとは仮定しない。

Qによる変換が全域の散乱解を別の散乱解へ写すことを証明する。
入出射振幅もQtildeで変換される。第十章の出射振幅の一意性から

    S Qtilde = Qtilde S
    SF Qtilde = Qtilde SF

を得る。さらに第十章のユニタリティと合わせて

    SF† Qtilde SF = Qtilde
    b† Qtilde b = a† Qtilde a、b = SF a

を証明する。Qがユニタリで自己共役とは限らない場合、この値は複素数だが、
その実部・虚部はそれぞれ保存される。これは散乱前後の振幅についての保存式である。

## 選択則

Qtilde u = η u、Qtilde v = ζ v、η ≠ ζ ならば

    u† SF v = 0

となることを証明する。ユニタリ行列の非零固有ベクトルについて、
固有値の絶対値が1であることも証明するので、この性質を追加仮定に置く必要はない。
Qtildeが対角である基底では、異なる固有値を持つ行列要素そのものがゼロとなる。

具体的な周期格子の並進は第四章の行列を使う。
任意の実数値関数gを許し、各層の相互作用を次のように構成する。

* 第一方向変調：V(n)=diag(g(n₁))、残る対称性Q=S₂。
* 対角方向変調：V(n)=diag(g(n₁+n₂))、残る対称性Q=S₁ S₂†。

これらの可換性を実際の行列から証明する。
χ=ZMod.stdAddCharを使う正規化フーリエモード

    e_(r,s)(n₁,n₂) = (1/N) χ(r n₁ + s n₂)

を定義し、そのノルム1、自由質量行列の固有ベクトル性、および
並進固有値χ(-s)、χ(-(r-s))を証明する。
これを外部固有基底へ変換し、左右双方の入出射について次を得る。

* V(n₁)の有限層では、sが異なるモード間の散乱振幅はゼロ。
* V(n₁+n₂)の有限層では、r-sが異なるモード間の散乱振幅はゼロ。

格子ラベルの等号・差はZMod Nにおける等号・差であり、法Nの条件である。
これらは任意のN≥1で証明する。N=1では異なるラベルを持つ条件が成立しない。
さらにN=3の非定数障壁について、全開チャネル条件と禁止遷移の具体例を証明する。

## 観測周波数と証明範囲

構成した散乱場がexp(-iωt)の時間依存を保つことと、散乱写像が
その時間並進の位相作用と可換であることを証明する。
これは固定周波数の定常散乱問題での主張であり、一般の時間依存初期値問題を
周波数の直積分へ分解する定理まで扱うものではない。

一般の相互作用について各内部準運動量や各外部波数が個別に保存されるとは主張しない。
対称性によって禁止されない遷移が、必ず非零になるとも主張しない。
本章の保証に直接用いるのは4次元多成分場の行列構造と散乱解の一意性であり、
追加の独立時間発展や物理的時計の同定を証明するものではない。

## 利用方法と検証環境

第一〜第十章を同じmathlibプロジェクト内に置き、先行章をコンパイルしてから：

    lake env lean -DwarningAsError=true Chapter11_InternalSymmetry.lean

Lean 4.24.0 / mathlib v4.24.0。
mathlibコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
本章はMathlib.Analysis.SpecialFunctions.Complex.CircleAddCharもインポートする。
末尾の #print axioms で主要定理の公理依存を確認する。
-/

noncomputable section
open scoped BigOperators ComplexOrder Topology
namespace TwelveDimensionalPhaseSpace
namespace InternalSymmetry
open StaticScattering WronskianFlux ScatteringUnitarity

/-! ## 補助：左右チャネルの直和とスペクトル関数 -/

section MatrixAlgebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def doubleMatrix (Q : Matrix ι ι ℂ) : Matrix (Sum ι ι) (Sum ι ι) ℂ :=
  Matrix.fromBlocks Q 0 0 Q

omit [DecidableEq ι] in
theorem doubleMatrix_mul (A B : Matrix ι ι ℂ) :
    doubleMatrix (A * B) = doubleMatrix A * doubleMatrix B := by
  simp [doubleMatrix, Matrix.fromBlocks_multiply]

omit [Fintype ι] [DecidableEq ι] in
theorem doubleMatrix_adjoint (Q : Matrix ι ι ℂ) :
    (doubleMatrix Q).conjTranspose = doubleMatrix Q.conjTranspose := by
  simp [doubleMatrix, Matrix.fromBlocks_conjTranspose]

omit [Fintype ι] in
theorem doubleMatrix_one : doubleMatrix (1 : Matrix ι ι ℂ) = 1 := by
  ext (i | i) (j | j) <;> simp [doubleMatrix, Matrix.one_apply]

theorem doubleMatrix_unitary (Q : Matrix ι ι ℂ) (hQ : IsUnitaryMatrix Q) :
    IsUnitaryMatrix (doubleMatrix Q) := by
  constructor
  · rw [doubleMatrix_adjoint, ← doubleMatrix_mul, hQ.1, doubleMatrix_one]
  · rw [doubleMatrix_adjoint, ← doubleMatrix_mul, hQ.2, doubleMatrix_one]

theorem unitary_adjoint (Q : Matrix ι ι ℂ) (hQ : IsUnitaryMatrix Q) :
    IsUnitaryMatrix Q.conjTranspose := by
  simpa only [IsUnitaryMatrix, Matrix.conjTranspose_conjTranspose] using And.symm hQ

theorem matrix_commutes_diagonal_function (A : Matrix ι ι ℂ) (d : ι → ℝ)
    (hA : A * Matrix.diagonal (fun i => (d i : ℂ)) =
      Matrix.diagonal (fun i => (d i : ℂ)) * A) (f : ℝ → ℂ) :
    A * Matrix.diagonal (fun i => f (d i)) = Matrix.diagonal (fun i => f (d i)) * A := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hA
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  by_cases hd : d i = d j
  · rw [hd, mul_comm]
  · have hz : A i j = 0 := by
      have hc : (d j : ℂ) - (d i : ℂ) ≠ 0 :=
        sub_ne_zero.mpr (fun h => hd (Complex.ofReal_injective h).symm)
      have hh : A i j * ((d j : ℂ) - (d i : ℂ)) = 0 := by
        rw [mul_sub, he, mul_comm (d i : ℂ), sub_self]
      exact (mul_eq_zero.mp hh).resolve_right hc
    simp only [hz, zero_mul, mul_zero]

theorem diagonal_action (d : ι → ℂ) (a : ι → ℂ) :
    (Matrix.diagonal d).mulVec a = fun i => d i * a i := by
  ext i
  exact Matrix.mulVec_diagonal _ _ _

theorem diagonal_multiplier_equivariance (A : Matrix ι ι ℂ) (d : ι → ℝ)
    (hA : A * Matrix.diagonal (fun i => (d i : ℂ)) =
      Matrix.diagonal (fun i => (d i : ℂ)) * A) (f : ℝ → ℂ) (a : ι → ℂ) :
    A.mulVec (fun i => f (d i) * a i) = fun i => f (d i) * A.mulVec a i := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M.mulVec a)
    (matrix_commutes_diagonal_function A d hA f)
  simpa only [← Matrix.mulVec_mulVec, diagonal_action] using h

end MatrixAlgebra

/-! ## 11.1　内部対称性の外部チャネル基底への変換 -/

section ExteriorSymmetry
variable {N : ℕ} [NeZero N]

def channelSymmetry (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (Q : InternalMatrix N) : InternalMatrix N :=
  (exteriorUnitary p s k).conjTranspose * Q * exteriorUnitary p s k

def scatteringSymmetry (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (Q : InternalMatrix N) : ScatteringMatrix N := doubleMatrix (channelSymmetry p s k Q)

theorem channelSymmetry_intertwines (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N) :
    exteriorUnitary p s k * channelSymmetry p s k Q = Q * exteriorUnitary p s k := by
  unfold channelSymmetry
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, (exteriorUnitary_unitary p s k).2, Matrix.one_mul]

theorem channelSymmetry_unitary (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N) (hQ : IsUnitaryMatrix Q) :
    IsUnitaryMatrix (channelSymmetry p s k Q) := by
  simpa only [Discretization.conjugateBy, Matrix.conjTranspose_conjTranspose] using
    Discretization.conjugateBy_unitary (exteriorUnitary p s k).conjTranspose Q
      (unitary_adjoint _ (exteriorUnitary_unitary p s k)) hQ

theorem scatteringSymmetry_unitary (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N) (hQ : IsUnitaryMatrix Q) :
    IsUnitaryMatrix (scatteringSymmetry p s k Q) :=
  doubleMatrix_unitary _ (channelSymmetry_unitary p s k Q hQ)

theorem exteriorDefect_diagonal (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) :
    (exteriorUnitary p s k).conjTranspose * exteriorDefect p s k * exteriorUnitary p s k =
      Matrix.diagonal (fun α => (channelDefect p s k α : ℂ)) := by
  exact (exteriorDefect_hermitian p s k).star_mul_self_mul_eq_diagonal

theorem channelSymmetry_commutes_defect (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N)
    (hQ : Q * freeMassSquared p s = freeMassSquared p s * Q) :
    channelSymmetry p s k Q * Matrix.diagonal (fun α => (channelDefect p s k α : ℂ)) =
      Matrix.diagonal (fun α => (channelDefect p s k α : ℂ)) * channelSymmetry p s k Q := by
  have hd : Q * exteriorDefect p s k = exteriorDefect p s k * Q := by
    simp only [exteriorDefect, Matrix.mul_sub, Matrix.sub_mul, realScalarMatrix,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, hQ]
  rw [← exteriorDefect_diagonal]
  unfold channelSymmetry
  calc
    _ = (exteriorUnitary p s k).conjTranspose * (Q * exteriorDefect p s k) *
        exteriorUnitary p s k := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (exteriorUnitary p s k)
        (exteriorUnitary p s k).conjTranspose, (exteriorUnitary_unitary p s k).2, Matrix.one_mul]
    _ = (exteriorUnitary p s k).conjTranspose * (exteriorDefect p s k * Q) *
        exteriorUnitary p s k := by rw [hd]
    _ = _ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (exteriorUnitary p s k)
        (exteriorUnitary p s k).conjTranspose, (exteriorUnitary_unitary p s k).2, Matrix.one_mul]

theorem channelSymmetry_multiplier (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N)
    (hQ : Q * freeMassSquared p s = freeMassSquared p s * Q)
    (f : ℝ → ℂ) (a : InternalVector N) :
    (channelSymmetry p s k Q).mulVec (fun α => f (channelDefect p s k α) * a α) =
      fun α => f (channelDefect p s k α) * (channelSymmetry p s k Q).mulVec a α :=
  diagonal_multiplier_equivariance _ _ (channelSymmetry_commutes_defect p s k Q hQ) f a

theorem exteriorProfile_equivariant (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N)
    (hQ : Q * freeMassSquared p s = freeMassSquared p s * Q)
    (a b : InternalVector N) (x : ℝ) :
    exteriorProfile p s k ((channelSymmetry p s k Q).mulVec a)
      ((channelSymmetry p s k Q).mulVec b) x = Q.mulVec (exteriorProfile p s k a b x) := by
  have hc : profileCoefficients p s k ((channelSymmetry p s k Q).mulVec a)
      ((channelSymmetry p s k Q).mulVec b) x =
      (channelSymmetry p s k Q).mulVec (profileCoefficients p s k a b x) := by
    unfold profileCoefficients
    rw [show (fun α => planeWave (channelWaveNumber p s k α) x * a α +
      planeWave (-channelWaveNumber p s k α) x * b α) =
      (fun α => planeWave (channelWaveNumber p s k α) x * a α) +
      (fun α => planeWave (-channelWaveNumber p s k α) x * b α) from rfl]
    simp only [channelWaveNumber]
    rw [Matrix.mulVec_add, channelSymmetry_multiplier p s k Q hQ
      (fun d => planeWave (Real.sqrt d) x), channelSymmetry_multiplier p s k Q hQ
      (fun d => planeWave (-Real.sqrt d) x)]
    rfl
  rw [exteriorProfile_repr, exteriorProfile_repr, hc, Matrix.mulVec_mulVec,
    channelSymmetry_intertwines, ← Matrix.mulVec_mulVec]

theorem exteriorSlope_equivariant (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N)
    (hQ : Q * freeMassSquared p s = freeMassSquared p s * Q)
    (a b : InternalVector N) (x : ℝ) :
    exteriorSlope p s k ((channelSymmetry p s k Q).mulVec a)
      ((channelSymmetry p s k Q).mulVec b) x = Q.mulVec (exteriorSlope p s k a b x) := by
  have hc : slopeCoefficients p s k ((channelSymmetry p s k Q).mulVec a)
      ((channelSymmetry p s k Q).mulVec b) x =
      (channelSymmetry p s k Q).mulVec (slopeCoefficients p s k a b x) := by
    unfold slopeCoefficients
    rw [show (fun α => phaseRate (channelWaveNumber p s k α) *
      planeWave (channelWaveNumber p s k α) x * a α +
      phaseRate (-channelWaveNumber p s k α) * planeWave (-channelWaveNumber p s k α) x * b α) =
      (fun α => (phaseRate (channelWaveNumber p s k α) * planeWave (channelWaveNumber p s k α) x) * a α) +
      (fun α => (phaseRate (-channelWaveNumber p s k α) * planeWave (-channelWaveNumber p s k α) x) * b α)
      from rfl]
    simp only [channelWaveNumber]
    rw [Matrix.mulVec_add, channelSymmetry_multiplier p s k Q hQ
      (fun d => phaseRate (Real.sqrt d) * planeWave (Real.sqrt d) x),
      channelSymmetry_multiplier p s k Q hQ
      (fun d => phaseRate (-Real.sqrt d) * planeWave (-Real.sqrt d) x)]
    rfl
  rw [exteriorSlope_repr, exteriorSlope_repr, hc, Matrix.mulVec_mulVec,
    channelSymmetry_intertwines, ← Matrix.mulVec_mulVec]

end ExteriorSymmetry

/-! ## 散乱解の変換と、一意性からの散乱行列の可換性 -/

section SolutionSymmetry
variable {N : ℕ} [NeZero N]

theorem doubleMatrix_pack (Q : InternalMatrix N) (f g : InternalVector N) :
    (doubleMatrix Q).mulVec (packState f g) = packState (Q.mulVec f) (Q.mulVec g) := by
  ext (n | n) <;> simp [doubleMatrix, Matrix.fromBlocks_mulVec, packState, Function.comp_def]

theorem doubleMatrix_left (Q : InternalMatrix N) (a : StateVector N) :
    (fun α => (doubleMatrix Q).mulVec a (Sum.inl α)) = Q.mulVec (fun α => a (Sum.inl α)) := by
  ext α
  simp [doubleMatrix, Matrix.fromBlocks_mulVec, Function.comp_def]

theorem doubleMatrix_right (Q : InternalMatrix N) (a : StateVector N) :
    (fun α => (doubleMatrix Q).mulVec a (Sum.inr α)) = Q.mulVec (fun α => a (Sum.inr α)) := by
  ext α
  simp [doubleMatrix, Matrix.fromBlocks_mulVec, Function.comp_def]

def mapAmplitudes (C : InternalMatrix N) (a : ExteriorAmplitudes N) : ExteriorAmplitudes N :=
  ⟨(doubleMatrix C).mulVec a.incoming, (doubleMatrix C).mulVec a.outgoing⟩

theorem leftExterior_equivariant (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N)
    (hQ : Q * freeMassSquared p s = freeMassSquared p s * Q)
    (a : ExteriorAmplitudes N) (x : ℝ) :
    leftExteriorState p s k (mapAmplitudes (channelSymmetry p s k Q) a) x =
      (doubleMatrix Q).mulVec (leftExteriorState p s k a x) := by
  simp only [leftExteriorState, mapAmplitudes, doubleMatrix_left, doubleMatrix_pack,
    exteriorProfile_equivariant p s k Q hQ, exteriorSlope_equivariant p s k Q hQ]

theorem rightExterior_equivariant (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N)
    (hQ : Q * freeMassSquared p s = freeMassSquared p s * Q)
    (width : ℝ) (a : ExteriorAmplitudes N) (x : ℝ) :
    rightExteriorState p s k width (mapAmplitudes (channelSymmetry p s k Q) a) x =
      (doubleMatrix Q).mulVec (rightExteriorState p s k width a x) := by
  simp only [rightExteriorState, mapAmplitudes, doubleMatrix_right, doubleMatrix_pack,
    exteriorProfile_equivariant p s k Q hQ, exteriorSlope_equivariant p s k Q hQ]

theorem layeredPotential_commutes (p : ModelParameters) (s : InternalShifts N)
    (layers : List (BarrierLayer N)) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q) (x : ℝ) :
    Q * layeredPotential layers x = layeredPotential layers x * Q := by
  simpa only [potentialFromLayers] using hQ.interactionCommute 0 (fun _ => x)

theorem coefficientAt_commutes (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q) (x : ℝ) :
    Q * coefficientAt p s k layers x = coefficientAt p s k layers x * Q := by
  simp only [coefficientAt, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    hQ.freeCommute, layeredPotential_commutes p s layers Q hQ x, realScalarMatrix,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem stationaryGenerator_commutes (Q C : InternalMatrix N) (hC : Q * C = C * Q) :
    doubleMatrix Q * stationaryGenerator C = stationaryGenerator C * doubleMatrix Q := by
  simp [doubleMatrix, stationaryGenerator, Matrix.fromBlocks_multiply, hC]

/-- 全接続点での連続性を含め、対称性変換した関数も第八章の散乱解である。 -/
theorem scatteringSolution_equivariant (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N)) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q)
    (a : ExteriorAmplitudes N) (y : ℝ → StateVector N)
    (hy : IsScatteringSolution p s k layers a y) :
    IsScatteringSolution p s k layers (mapAmplitudes (channelSymmetry p s k Q) a)
      (fun x => (doubleMatrix Q).mulVec (y x)) := by
  refine ⟨(matrixGenerator (doubleMatrix Q)).continuous.comp hy.1, ?_, ?_, ?_⟩
  · intro x hx
    have hd := (matrixGenerator (doubleMatrix Q)).hasFDerivAt.comp_hasDerivAt x (hy.2.1 x hx)
    change HasDerivAt (fun t => (doubleMatrix Q).mulVec (y t))
      ((doubleMatrix Q).mulVec ((stationaryGenerator (coefficientAt p s k layers x)).mulVec (y x))) x at hd
    rw [Matrix.mulVec_mulVec, stationaryGenerator_commutes Q _
      (coefficientAt_commutes p s k layers Q hQ x), ← Matrix.mulVec_mulVec] at hd
    exact hd
  · intro x hx
    change (doubleMatrix Q).mulVec (y x) = _
    rw [hy.2.2.1 x hx, leftExterior_equivariant p s k Q hQ.freeCommute]
  · intro x hx
    change (doubleMatrix Q).mulVec (y x) = _
    rw [hy.2.2.2 x hx, rightExterior_equivariant p s k Q hQ.freeCommute]

/-- 境界値問題の出射振幅の一意性から、未規格化散乱行列の可換性を導く。 -/
theorem scatteringMatrix_commutes (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q) :
    scatteringMatrix p s k layers hOpen * scatteringSymmetry p s k Q =
      scatteringSymmetry p s k Q * scatteringMatrix p s k layers hOpen := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro a
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  have hy := scatteringMatrix_solution_exists p s k layers hOpen a
  have ht := scatteringSolution_equivariant p s k layers Q hQ _ _ hy
  exact (scattering_outgoing_unique p s k layers hOpen
    ((scatteringSymmetry p s k Q).mulVec a)
    ((scatteringSymmetry p s k Q).mulVec ((scatteringMatrix p s k layers hOpen).mulVec a)) _ ht).symm

end SolutionSymmetry

/-! ## 流束規格化との両立と、散乱前後の保存量 -/

section FluxSymmetry
variable {N : ℕ} [NeZero N]

theorem channelSymmetry_commutes_function (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N)
    (hQ : Q * freeMassSquared p s = freeMassSquared p s * Q) (f : ℝ → ℂ) :
    channelSymmetry p s k Q * Matrix.diagonal (fun α => f (channelDefect p s k α)) =
      Matrix.diagonal (fun α => f (channelDefect p s k α)) * channelSymmetry p s k Q :=
  matrix_commutes_diagonal_function _ _ (channelSymmetry_commutes_defect p s k Q hQ) f

theorem channelSymmetry_commutes_waveNumber (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N)
    (hQ : Q * freeMassSquared p s = freeMassSquared p s * Q) :
    channelSymmetry p s k Q * Matrix.diagonal (fun α => (channelWaveNumber p s k α : ℂ)) =
      Matrix.diagonal (fun α => (channelWaveNumber p s k α : ℂ)) * channelSymmetry p s k Q :=
  channelSymmetry_commutes_function p s k Q hQ (fun d => (Real.sqrt d : ℂ))

theorem weightRoot_double (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    weightRoot (channelWeight p s k) = doubleMatrix
      (Matrix.diagonal (fun α => (Real.sqrt (channelWaveNumber p s k α) : ℂ))) := by
  ext (i | i) (j | j) <;> simp [weightRoot, channelWeight, doubleMatrix, Matrix.diagonal_apply]

theorem weightRootInv_double (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters) :
    weightRootInv (channelWeight p s k) = doubleMatrix
      (Matrix.diagonal (fun α => (Real.sqrt (channelWaveNumber p s k α) : ℂ)⁻¹)) := by
  ext (i | i) (j | j) <;> simp [weightRootInv, channelWeight, doubleMatrix, Matrix.diagonal_apply]

theorem scatteringSymmetry_commutes_weightRoot (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N)
    (hQ : Q * freeMassSquared p s = freeMassSquared p s * Q) :
    scatteringSymmetry p s k Q * weightRoot (channelWeight p s k) =
      weightRoot (channelWeight p s k) * scatteringSymmetry p s k Q := by
  rw [weightRoot_double, scatteringSymmetry, ← doubleMatrix_mul, ← doubleMatrix_mul]
  exact congrArg doubleMatrix
    (channelSymmetry_commutes_function p s k Q hQ (fun d => (Real.sqrt (Real.sqrt d) : ℂ)))

theorem scatteringSymmetry_commutes_weightRootInv (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N)
    (hQ : Q * freeMassSquared p s = freeMassSquared p s * Q) :
    scatteringSymmetry p s k Q * weightRootInv (channelWeight p s k) =
      weightRootInv (channelWeight p s k) * scatteringSymmetry p s k Q := by
  rw [weightRootInv_double, scatteringSymmetry, ← doubleMatrix_mul, ← doubleMatrix_mul]
  exact congrArg doubleMatrix
    (channelSymmetry_commutes_function p s k Q hQ (fun d => (Real.sqrt (Real.sqrt d) : ℂ)⁻¹))

/-- 流束規格化後も同じ残存対称性が成り立つ。 -/
theorem fluxNormalizedScatteringMatrix_commutes (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q) :
    fluxNormalizedScatteringMatrix p s k layers hOpen * scatteringSymmetry p s k Q =
      scatteringSymmetry p s k Q * fluxNormalizedScatteringMatrix p s k layers hOpen := by
  let C := scatteringSymmetry p s k Q
  let W := weightRoot (channelWeight p s k)
  let Wi := weightRootInv (channelWeight p s k)
  let S := scatteringMatrix p s k layers hOpen
  have hW : C * W = W * C := scatteringSymmetry_commutes_weightRoot p s k Q hQ.freeCommute
  have hi : C * Wi = Wi * C := scatteringSymmetry_commutes_weightRootInv p s k Q hQ.freeCommute
  have hS : S * C = C * S := scatteringMatrix_commutes p s k layers hOpen Q hQ
  change W * S * Wi * C = C * (W * S * Wi)
  calc
    _ = W * S * (Wi * C) := by rw [Matrix.mul_assoc]
    _ = W * S * (C * Wi) := by rw [← hi]
    _ = W * (S * C) * Wi := by noncomm_ring
    _ = W * (C * S) * Wi := by rw [hS]
    _ = (W * C) * S * Wi := by noncomm_ring
    _ = (C * W) * S * Wi := by rw [← hW]
    _ = _ := by noncomm_ring

theorem scattering_symmetry_form_conserved (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q) :
    (fluxNormalizedScatteringMatrix p s k layers hOpen).conjTranspose *
      scatteringSymmetry p s k Q * fluxNormalizedScatteringMatrix p s k layers hOpen =
      scatteringSymmetry p s k Q := by
  have hc := fluxNormalizedScatteringMatrix_commutes p s k layers hOpen Q hQ
  have hu := (fluxNormalizedScatteringMatrix_unitary p s k layers hOpen).1
  calc
    _ = (fluxNormalizedScatteringMatrix p s k layers hOpen).conjTranspose *
        (fluxNormalizedScatteringMatrix p s k layers hOpen * scatteringSymmetry p s k Q) := by
      rw [Matrix.mul_assoc, ← hc]
    _ = _ := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]

/-- a=bとすれば対称性の期待値の保存式。実部・虚部もそれぞれ等しい。 -/
theorem scattering_symmetry_pairing_conserved (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q) (a b : StateVector N) :
    star ((fluxNormalizedScatteringMatrix p s k layers hOpen).mulVec a) ⬝ᵥ
      (scatteringSymmetry p s k Q).mulVec ((fluxNormalizedScatteringMatrix p s k layers hOpen).mulVec b) =
      star a ⬝ᵥ (scatteringSymmetry p s k Q).mulVec b := by
  change form (scatteringSymmetry p s k Q)
    ((fluxNormalizedScatteringMatrix p s k layers hOpen).mulVec a)
    ((fluxNormalizedScatteringMatrix p s k layers hOpen).mulVec b) =
      form (scatteringSymmetry p s k Q) a b
  rw [form_congruence, scattering_symmetry_form_conserved p s k layers hOpen Q hQ]

end FluxSymmetry

/-! ## 11.2　異なる対称性固有値の間の禁止遷移 -/

section SelectionAlgebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitary_pairing_general (Q : Matrix ι ι ℂ) (hQ : IsUnitaryMatrix Q) (u v : ι → ℂ) :
    star (Q.mulVec u) ⬝ᵥ (Q.mulVec v) = star u ⬝ᵥ v := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    hQ.1, Matrix.vecMul_one]

omit [DecidableEq ι] in
theorem pairing_self_squareNorm (a : ι → ℂ) : star a ⬝ᵥ a = (squareNorm a : ℂ) := by
  unfold squareNorm dotProduct
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  exact Complex.normSq_eq_conj_mul_self.symm

theorem squareNorm_unitary (Q : Matrix ι ι ℂ) (hQ : IsUnitaryMatrix Q) (a : ι → ℂ) :
    squareNorm (Q.mulVec a) = squareNorm a := by
  have h := congrArg Complex.re (unitary_pairing_general Q hQ a a)
  simpa only [pairing_self_squareNorm, Complex.ofReal_re] using h

omit [DecidableEq ι] in
theorem matrix_preserves_eigenspace (S Q : Matrix ι ι ℂ) (hSQ : S * Q = Q * S)
    (a : ι → ℂ) (ζ : ℂ) (ha : Q.mulVec a = ζ • a) :
    Q.mulVec (S.mulVec a) = ζ • S.mulVec a := by
  rw [Matrix.mulVec_mulVec, ← hSQ, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul]

theorem eigenphase_transition_zero (S Q : Matrix ι ι ℂ) (hQ : IsUnitaryMatrix Q)
    (hSQ : S * Q = Q * S) (u v : ι → ℂ) (η ζ : ℂ)
    (hη : η * star η = 1) (hu : Q.mulVec u = η • u) (hv : Q.mulVec v = ζ • v)
    (hne : ζ ≠ η) : star u ⬝ᵥ (S.mulVec v) = 0 := by
  have he := unitary_pairing_general Q hQ u (S.mulVec v)
  rw [hu, matrix_preserves_eigenspace S Q hSQ v ζ hv] at he
  simp only [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at he
  have hm : ζ * (star u ⬝ᵥ S.mulVec v) = η * (star u ⬝ᵥ S.mulVec v) := by
    calc
      _ = (η * star η) * (ζ * (star u ⬝ᵥ S.mulVec v)) := by rw [hη, one_mul]
      _ = η * (ζ * (star η * (star u ⬝ᵥ S.mulVec v))) := by ring
      _ = _ := congrArg (fun z : ℂ => η * z) he
  have hz : (ζ - η) * (star u ⬝ᵥ S.mulVec v) = 0 := by
    rw [sub_mul, hm, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

theorem unitary_eigenvalue_phase (Q : Matrix ι ι ℂ) (hQ : IsUnitaryMatrix Q)
    (u : ι → ℂ) (η : ℂ) (hu : Q.mulVec u = η • u) (hne : u ≠ 0) : η * star η = 1 := by
  have hn : star u ⬝ᵥ u ≠ 0 := fun h => hne (dotProduct_star_self_eq_zero.mp h)
  have he := unitary_pairing_general Q hQ u u
  rw [hu] at he
  simp only [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at he
  have hz : (η * star η - 1) * (star u ⬝ᵥ u) = 0 := by
    calc
      _ = η * (star η * (star u ⬝ᵥ u)) - star u ⬝ᵥ u := by ring
      _ = 0 := sub_eq_zero.mpr he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hn)

theorem eigenvalue_transition_zero (S Q : Matrix ι ι ℂ) (hQ : IsUnitaryMatrix Q)
    (hSQ : S * Q = Q * S) (u v : ι → ℂ) (η ζ : ℂ)
    (hu : Q.mulVec u = η • u) (hv : Q.mulVec v = ζ • v) (hne : ζ ≠ η) :
    star u ⬝ᵥ (S.mulVec v) = 0 := by
  by_cases hz : u = 0
  · simp [hz]
  · exact eigenphase_transition_zero S Q hQ hSQ u v η ζ
      (unitary_eigenvalue_phase Q hQ u η hu hz) hu hv hne

theorem diagonal_charge_entry_zero (S : Matrix ι ι ℂ) (q : ι → ℂ)
    (hS : S * Matrix.diagonal q = Matrix.diagonal q * S) (i j : ι) (hij : q i ≠ q j) :
    S i j = 0 := by
  have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hS
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  have hz : S i j * (q j - q i) = 0 := by
    rw [mul_sub, he, mul_comm (q i), sub_self]
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hij.symm)

end SelectionAlgebra

/-! ## 第十章の散乱行列への選択則の適用 -/

section ScatteringSelection
variable {N : ℕ} [NeZero N]

theorem scattering_preserves_symmetry_eigenspace (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q)
    (a : StateVector N) (ζ : ℂ) (ha : (scatteringSymmetry p s k Q).mulVec a = ζ • a) :
    (scatteringSymmetry p s k Q).mulVec ((fluxNormalizedScatteringMatrix p s k layers hOpen).mulVec a) =
      ζ • (fluxNormalizedScatteringMatrix p s k layers hOpen).mulVec a :=
  matrix_preserves_eigenspace _ _ (fluxNormalizedScatteringMatrix_commutes p s k layers hOpen Q hQ) a ζ ha

theorem scattering_eigenphase_transition_zero (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q)
    (u v : StateVector N) (η ζ : ℂ) (hη : η * star η = 1)
    (hu : (scatteringSymmetry p s k Q).mulVec u = η • u)
    (hv : (scatteringSymmetry p s k Q).mulVec v = ζ • v) (hne : ζ ≠ η) :
    star u ⬝ᵥ ((fluxNormalizedScatteringMatrix p s k layers hOpen).mulVec v) = 0 :=
  eigenphase_transition_zero _ _ (scatteringSymmetry_unitary p s k Q hQ.unitary)
    (fluxNormalizedScatteringMatrix_commutes p s k layers hOpen Q hQ) u v η ζ hη hu hv hne

/-- 固有値の単位絶対値を別途仮定せず、異なる固有値の間の散乱振幅をゼロとする。 -/
theorem scattering_eigenvalue_transition_zero (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q)
    (u v : StateVector N) (η ζ : ℂ)
    (hu : (scatteringSymmetry p s k Q).mulVec u = η • u)
    (hv : (scatteringSymmetry p s k Q).mulVec v = ζ • v) (hne : ζ ≠ η) :
    star u ⬝ᵥ ((fluxNormalizedScatteringMatrix p s k layers hOpen).mulVec v) = 0 :=
  eigenvalue_transition_zero _ _ (scatteringSymmetry_unitary p s k Q hQ.unitary)
    (fluxNormalizedScatteringMatrix_commutes p s k layers hOpen Q hQ) u v η ζ hu hv hne

theorem scattering_entry_zero_of_diagonalSymmetry (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (Q : InternalMatrix N)
    (hQ : SymmetryHypotheses p s (potentialFromLayers layers) Q)
    (q : ScatteringChannel N → ℂ) (hq : scatteringSymmetry p s k Q = Matrix.diagonal q)
    (i j : ScatteringChannel N) (hij : q i ≠ q j) :
    fluxNormalizedScatteringMatrix p s k layers hOpen i j = 0 := by
  apply diagonal_charge_entry_zero _ q _ i j hij
  rw [← hq]
  exact fluxNormalizedScatteringMatrix_commutes p s k layers hOpen Q hQ

end ScatteringSelection

/-! ## 格子上の相互作用と残存対称性の具体的構成 -/

section ConcreteBarriers
variable {N : ℕ} [NeZero N]
open Lattice

theorem shiftBy_diagonal_commutes (r : Grid N) (f : Grid N → ℂ)
    (hf : ∀ n, f (n - r) = f n) :
    shiftBy r * Matrix.diagonal f = Matrix.diagonal f * shiftBy r := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, shiftBy_mulVec, diagonal_action]
  ext n
  simp only [hf]

theorem shiftBy_freeMassSquared_commutes (p : ModelParameters) (r : Grid N) :
    shiftBy r * freeMassSquared p (concreteInternalShifts N) =
      freeMassSquared p (concreteInternalShifts N) * shiftBy r := by
  simp only [freeMassSquared, internalLaplacian, realScalarMatrix, concreteInternalShifts,
    firstShift, secondShift, shiftBy_adjoint, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, shiftBy_commute r (firstDirection N), shiftBy_commute r (secondDirection N),
    shiftBy_commute r (-firstDirection N), shiftBy_commute r (-secondDirection N)]

theorem layeredPotential_commutes_of_layers (Q : InternalMatrix N)
    (layers : List (BarrierLayer N))
    (hQ : ∀ l ∈ layers, Q * l.value = l.value * Q) (x : ℝ) :
    Q * layeredPotential layers x = layeredPotential layers x * Q := by
  induction layers generalizing x with
  | nil => simp only [layeredPotential, Matrix.mul_zero, Matrix.zero_mul]
  | cons l rest ih =>
    by_cases hneg : x < 0
    · simp only [layeredPotential, if_pos hneg, Matrix.mul_zero, Matrix.zero_mul]
    · by_cases hwidth : x < l.width
      · simp only [layeredPotential, if_neg hneg, if_pos hwidth]
        exact hQ l (List.mem_cons_self ..)
      · simp only [layeredPotential, if_neg hneg, if_neg hwidth]
        exact ih (fun m hm => hQ m (List.mem_cons_of_mem l hm)) (x - l.width)

structure ScalarLayerProfile (N : ℕ) where
  width : ℝ
  width_pos : 0 < width
  profile : ZMod N → ℝ

def firstModulatedLayer (b : ScalarLayerProfile N) : BarrierLayer N where
  width := b.width
  width_pos := b.width_pos
  value := Matrix.diagonal (fun n => (b.profile n.1 : ℂ))
  hermitian := by
    change (Matrix.diagonal (fun n : Grid N => (b.profile n.1 : ℂ))).conjTranspose = _
    simp

def diagonalModulatedLayer (b : ScalarLayerProfile N) : BarrierLayer N where
  width := b.width
  width_pos := b.width_pos
  value := Matrix.diagonal (fun n => (b.profile (n.1 + n.2) : ℂ))
  hermitian := by
    change (Matrix.diagonal (fun n : Grid N => (b.profile (n.1 + n.2) : ℂ))).conjTranspose = _
    simp

def diagonalShift (N : ℕ) [NeZero N] : InternalMatrix N := shiftBy (1, -1)

theorem diagonalShift_eq : diagonalShift N = firstShift N * (secondShift N).conjTranspose := by
  rw [diagonalShift, firstShift, secondShift, shiftBy_adjoint, shiftBy_add]
  congr 1
  ext <;> simp [firstDirection, secondDirection]

theorem firstModulatedLayer_commutes (b : ScalarLayerProfile N) :
    secondShift N * (firstModulatedLayer b).value =
      (firstModulatedLayer b).value * secondShift N := by
  apply shiftBy_diagonal_commutes
  intro n
  change (b.profile (n.1 - 0) : ℂ) = b.profile n.1
  rw [sub_zero]

theorem diagonalModulatedLayer_commutes (b : ScalarLayerProfile N) :
    diagonalShift N * (diagonalModulatedLayer b).value =
      (diagonalModulatedLayer b).value * diagonalShift N := by
  apply shiftBy_diagonal_commutes
  intro n
  change (b.profile ((n.1 - 1) + (n.2 - -1)) : ℂ) = b.profile (n.1 + n.2)
  congr 2
  ring

theorem firstModulated_symmetry (p : ModelParameters) (profiles : List (ScalarLayerProfile N)) :
    SymmetryHypotheses p (concreteInternalShifts N)
      (potentialFromLayers (profiles.map firstModulatedLayer)) (secondShift N) := by
  refine ⟨shiftBy_unitary _, shiftBy_freeMassSquared_commutes p _, ?_⟩
  intro τ x
  apply layeredPotential_commutes_of_layers
  intro l hl
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hl
  exact firstModulatedLayer_commutes b

theorem diagonalModulated_symmetry (p : ModelParameters) (profiles : List (ScalarLayerProfile N)) :
    SymmetryHypotheses p (concreteInternalShifts N)
      (potentialFromLayers (profiles.map diagonalModulatedLayer)) (diagonalShift N) := by
  refine ⟨shiftBy_unitary _, shiftBy_freeMassSquared_commutes p _, ?_⟩
  intro τ x
  apply layeredPotential_commutes_of_layers
  intro l hl
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hl
  exact diagonalModulatedLayer_commutes b

end ConcreteBarriers

/-! ## 周期格子のフーリエモードとs・r-sの保存 -/

section FourierModes
variable {N : ℕ} [NeZero N]
open Lattice

def characterMode (q : Grid N) : InternalVector N := fun n =>
  ZMod.stdAddChar (q.1 * n.1 + q.2 * n.2)

def fourierMode (q : Grid N) : InternalVector N := (N : ℂ)⁻¹ • characterMode q

def modeShiftPhase (q r : Grid N) : ℂ :=
  ZMod.stdAddChar (-(q.1 * r.1 + q.2 * r.2))

theorem shiftBy_characterMode (q r : Grid N) :
    (shiftBy r).mulVec (characterMode q) = modeShiftPhase q r • characterMode q := by
  rw [shiftBy_mulVec]
  ext n
  change ZMod.stdAddChar (q.1 * (n.1 - r.1) + q.2 * (n.2 - r.2)) =
    ZMod.stdAddChar (-(q.1 * r.1 + q.2 * r.2)) * ZMod.stdAddChar (q.1 * n.1 + q.2 * n.2)
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem shiftBy_fourierMode (q r : Grid N) :
    (shiftBy r).mulVec (fourierMode q) = modeShiftPhase q r • fourierMode q := by
  rw [fourierMode, Matrix.mulVec_smul, shiftBy_characterMode, smul_comm]

theorem secondShift_fourierMode (q : Grid N) :
    (secondShift N).mulVec (fourierMode q) = ZMod.stdAddChar (-q.2) • fourierMode q := by
  simpa only [secondShift, secondDirection, modeShiftPhase, mul_zero, mul_one, zero_add] using
    shiftBy_fourierMode q (secondDirection N)

theorem diagonalShift_fourierMode (q : Grid N) :
    (diagonalShift N).mulVec (fourierMode q) =
      ZMod.stdAddChar (-(q.1 - q.2)) • fourierMode q := by
  simpa only [diagonalShift, modeShiftPhase, mul_one, mul_neg, sub_eq_add_neg] using
    shiftBy_fourierMode q (1, -1)

theorem stdAddChar_unit (x : ZMod N) :
    ZMod.stdAddChar x * star (ZMod.stdAddChar x) = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact (Complex.mul_conj _).trans (by simp)

theorem characterMode_normSq (q : Grid N) (n : Grid N) : Complex.normSq (characterMode q n) = 1 := by
  simp only [characterMode, ZMod.stdAddChar_apply, Circle.normSq_coe]

theorem fourierMode_normalized (q : Grid N) : squareNorm (fourierMode q) = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [squareNorm, fourierMode, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀,
    characterMode_normSq, mul_one]
  simp [Complex.normSq_natCast, Fintype.card_prod, hN, ← sq]

def fourierMassSquared (p : ModelParameters) (q : Grid N) : ℂ :=
  (p.massParameter ^ 2 : ℝ) - ((p.latticeSpacing ^ 2)⁻¹ : ℝ) *
    ((2 - modeShiftPhase q (firstDirection N) - modeShiftPhase q (-firstDirection N)) +
      (2 - modeShiftPhase q (secondDirection N) - modeShiftPhase q (-secondDirection N)))

theorem fourierMode_mass_eigenvector (p : ModelParameters) (q : Grid N) :
    (freeMassSquared p (concreteInternalShifts N)).mulVec (fourierMode q) =
      fourierMassSquared p q • fourierMode q := by
  simp only [freeMassSquared, internalLaplacian, concreteInternalShifts, firstShift,
    secondShift, shiftBy_adjoint, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    realScalarMatrix, Matrix.one_mulVec, shiftBy_fourierMode]
  ext n
  simp only [fourierMassSquared, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    Complex.real_smul, smul_eq_mul]
  ring

theorem channelSymmetry_coordinates (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N) :
    channelSymmetry p s k Q * (exteriorUnitary p s k).conjTranspose =
      (exteriorUnitary p s k).conjTranspose * Q := by
  unfold channelSymmetry
  rw [Matrix.mul_assoc, Matrix.mul_assoc, (exteriorUnitary_unitary p s k).2, Matrix.mul_one]

theorem channelSymmetry_eigenvector (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N) (v : InternalVector N) (ζ : ℂ)
    (hv : Q.mulVec v = ζ • v) :
    (channelSymmetry p s k Q).mulVec ((exteriorUnitary p s k).conjTranspose.mulVec v) =
      ζ • (exteriorUnitary p s k).conjTranspose.mulVec v := by
  rw [Matrix.mulVec_mulVec, channelSymmetry_coordinates, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

def sideVector (rightSide : Bool) (v : InternalVector N) : StateVector N :=
  if rightSide then packState 0 v else packState v 0

theorem doubleMatrix_sideVector (Q : InternalMatrix N) (side : Bool) (v : InternalVector N) :
    (doubleMatrix Q).mulVec (sideVector side v) = sideVector side (Q.mulVec v) := by
  cases side <;> simp [sideVector, doubleMatrix_pack]

omit [NeZero N] in
theorem sideVector_smul (side : Bool) (v : InternalVector N) (ζ : ℂ) :
    sideVector side (ζ • v) = ζ • sideVector side v := by
  cases side <;> ext (n | n) <;> simp [sideVector, packState]

def channelMode (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (side : Bool) (q : Grid N) : StateVector N :=
  sideVector side ((exteriorUnitary p s k).conjTranspose.mulVec (fourierMode q))

theorem channelMode_normalized (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (side : Bool) (q : Grid N) :
    squareNorm (channelMode p s k side q) = 1 := by
  have h := squareNorm_unitary _ (unitary_adjoint _ (exteriorUnitary_unitary p s k)) (fourierMode q)
  rw [fourierMode_normalized] at h
  cases side <;> simpa [channelMode, sideVector, packState, squareNorm,
    Fintype.sum_sum_type] using h

theorem channelMode_eigenvector (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (Q : InternalMatrix N) (side : Bool) (q : Grid N) (ζ : ℂ)
    (hq : Q.mulVec (fourierMode q) = ζ • fourierMode q) :
    (scatteringSymmetry p s k Q).mulVec (channelMode p s k side q) =
      ζ • channelMode p s k side q := by
  rw [channelMode, scatteringSymmetry, doubleMatrix_sideVector,
    channelSymmetry_eigenvector p s k Q _ ζ hq, sideVector_smul]

def modeTransition (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (hOpen : AllExteriorChannelsOpen p s k)
    (outSide inSide : Bool) (outLabel inLabel : Grid N) : ℂ :=
  star (channelMode p s k outSide outLabel) ⬝ᵥ
    ((fluxNormalizedScatteringMatrix p s k layers hOpen).mulVec (channelMode p s k inSide inLabel))

/-- 第一方向変調について第二方向格子量子数sの選択則。左右の全組合せを含む。 -/
theorem firstModulated_transition_zero (p : ModelParameters) (k : ScatteringParameters)
    (profiles : List (ScalarLayerProfile N))
    (hOpen : AllExteriorChannelsOpen p (concreteInternalShifts N) k)
    (outSide inSide : Bool) (outLabel inLabel : Grid N) (hne : inLabel.2 ≠ outLabel.2) :
    modeTransition p (concreteInternalShifts N) k (profiles.map firstModulatedLayer)
      hOpen outSide inSide outLabel inLabel = 0 := by
  apply scattering_eigenphase_transition_zero p (concreteInternalShifts N) k
    (profiles.map firstModulatedLayer) hOpen (secondShift N) (firstModulated_symmetry p profiles)
    _ _ (ZMod.stdAddChar (-outLabel.2)) (ZMod.stdAddChar (-inLabel.2)) (stdAddChar_unit _)
  · exact channelMode_eigenvector p _ k _ outSide outLabel _ (secondShift_fourierMode outLabel)
  · exact channelMode_eigenvector p _ k _ inSide inLabel _ (secondShift_fourierMode inLabel)
  · exact fun he => hne (neg_injective (ZMod.injective_stdAddChar he))

/-- 対角方向変調についてr-s mod Nの選択則。左右の全組合せを含む。 -/
theorem diagonalModulated_transition_zero (p : ModelParameters) (k : ScatteringParameters)
    (profiles : List (ScalarLayerProfile N))
    (hOpen : AllExteriorChannelsOpen p (concreteInternalShifts N) k)
    (outSide inSide : Bool) (outLabel inLabel : Grid N)
    (hne : inLabel.1 - inLabel.2 ≠ outLabel.1 - outLabel.2) :
    modeTransition p (concreteInternalShifts N) k (profiles.map diagonalModulatedLayer)
      hOpen outSide inSide outLabel inLabel = 0 := by
  apply scattering_eigenphase_transition_zero p (concreteInternalShifts N) k
    (profiles.map diagonalModulatedLayer) hOpen (diagonalShift N) (diagonalModulated_symmetry p profiles)
    _ _ (ZMod.stdAddChar (-(outLabel.1 - outLabel.2)))
    (ZMod.stdAddChar (-(inLabel.1 - inLabel.2))) (stdAddChar_unit _)
  · exact channelMode_eigenvector p _ k _ outSide outLabel _ (diagonalShift_fourierMode outLabel)
  · exact channelMode_eigenvector p _ k _ inSide inLabel _ (diagonalShift_fourierMode inLabel)
  · exact fun he => hne (neg_injective (ZMod.injective_stdAddChar he))

end FourierModes

/-! ## 11.3　観測時間の並進と固定周波数セクター -/

section ObservedFrequency
variable {N : ℕ} [NeZero N]

theorem observed_planeWave_add (a x y : ℝ) :
    planeWave a (x + y) = planeWave a x * planeWave a y := by
  simp only [planeWave, Complex.ofReal_add, mul_add, Complex.exp_add]

omit [NeZero N] in
theorem separatedField_timeTranslation (k : ScatteringParameters) (f : ℝ → InternalVector N)
    (τ Δ : ObservedTime) (x : SpatialPosition) :
    separatedField k f (τ + Δ) x = planeWave (-k.frequency) Δ • separatedField k f τ x := by
  ext n
  simp only [separatedField, planeFactor, observed_planeWave_add, Pi.smul_apply, smul_eq_mul]
  ring

omit [NeZero N] in
theorem separatedField_hasTimeDerivAt (k : ScatteringParameters) (f : ℝ → InternalVector N)
    (τ : ObservedTime) (x : SpatialPosition) (n : Grid N) :
    HasDerivAt (fun t => separatedField k f t x n)
      (phaseRate (-k.frequency) * separatedField k f τ x n) τ := by
  let C := planeWave (k.transverseMomentum 0) (x 1) *
    planeWave (k.transverseMomentum 1) (x 2) * f (x 0) n
  have hd := (planeWave_hasDerivAt (-k.frequency) τ).mul_const C
  convert hd using 1
  · funext t
    simp only [C, separatedField, planeFactor, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [C, separatedField, planeFactor, Pi.smul_apply, smul_eq_mul]
    ring

def observedScatteringField (p : ModelParameters) (s : InternalShifts N) (k : ScatteringParameters)
    (layers : List (BarrierLayer N)) (hOpen : AllExteriorChannelsOpen p s k) (a : StateVector N) :
    CoordinateField N :=
  separatedField k (fun x => stateValue (assembledScatteringState p s k layers
    ⟨a, (scatteringMatrix p s k layers hOpen).mulVec a⟩ x))

theorem scatteringField_timeTranslation (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a : StateVector N)
    (τ Δ : ObservedTime) (x : SpatialPosition) :
    observedScatteringField p s k layers hOpen a (τ + Δ) x =
      planeWave (-k.frequency) Δ • observedScatteringField p s k layers hOpen a τ x :=
  separatedField_timeTranslation k _ τ Δ x

theorem scatteringField_frequencyEigenvector (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a : StateVector N)
    (τ : ObservedTime) (x : SpatialPosition) (n : Grid N) :
    HasDerivAt (fun t => observedScatteringField p s k layers hOpen a t x n)
      (phaseRate (-k.frequency) * observedScatteringField p s k layers hOpen a τ x n) τ :=
  separatedField_hasTimeDerivAt k _ τ x n

theorem scattering_timeTranslation_covariance (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (layers : List (BarrierLayer N))
    (hOpen : AllExteriorChannelsOpen p s k) (a : StateVector N) (Δ : ObservedTime) :
    (scatteringMatrix p s k layers hOpen).mulVec (planeWave (-k.frequency) Δ • a) =
      planeWave (-k.frequency) Δ • (scatteringMatrix p s k layers hOpen).mulVec a :=
  Matrix.mulVec_smul _ _ _

end ObservedFrequency

/-! ## 仮定を満たす模型と3×3周期格子での具体例 -/

section RealizedExamples
variable {N : ℕ} [NeZero N]
open Lattice

/-- 全開チャネル条件が実現可能であることを、ラプラシアンの半正定値性から示す。 -/
theorem allExteriorChannelsOpen_of_frequency_bound (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) (hk : p.massParameter ^ 2 < reducedFrequencySquared k) :
    AllExteriorChannelsOpen p s k := by
  have he : realScalarMatrix (reducedFrequencySquared k) - freeMassSquared p s =
      realScalarMatrix (reducedFrequencySquared k - p.massParameter ^ 2) + internalLaplacian p s := by
    rw [freeMassSquared, MassMatrix.scalarMatrix_sub]
    abel
  change (realScalarMatrix (reducedFrequencySquared k) - freeMassSquared p s).PosDef
  rw [he]
  exact (MassMatrix.scalarMatrix_posDef (sub_pos.mpr hk)).add_posSemidef
    (internalLaplacian_posSemidef p s)

def referenceScatteringParameters : ScatteringParameters where
  frequency := 2
  frequency_pos := by norm_num
  transverseMomentum := 0

theorem referenceChannelsOpen (N : ℕ) [NeZero N] :
    AllExteriorChannelsOpen referenceParameters (concreteInternalShifts N) referenceScatteringParameters := by
  apply allExteriorChannelsOpen_of_frequency_bound
  norm_num [referenceParameters, referenceScatteringParameters, reducedFrequencySquared]

def referenceProfile (N : ℕ) : ScalarLayerProfile N where
  width := 1
  width_pos := by norm_num
  profile := fun j => if j = 0 then 1 else 0

theorem referenceProfile_nonconstant :
    (referenceProfile 3).profile 0 ≠ (referenceProfile 3).profile 1 := by
  norm_num [referenceProfile]

theorem referenceFirst_forbidden_transition :
    modeTransition referenceParameters (concreteInternalShifts 3) referenceScatteringParameters
      [firstModulatedLayer (referenceProfile 3)] (referenceChannelsOpen 3)
      false false (0, 0) (0, 1) = 0 := by
  exact firstModulated_transition_zero referenceParameters referenceScatteringParameters
    [referenceProfile 3] (referenceChannelsOpen 3) false false (0, 0) (0, 1) (by norm_num)

theorem referenceDiagonal_forbidden_transition :
    modeTransition referenceParameters (concreteInternalShifts 3) referenceScatteringParameters
      [diagonalModulatedLayer (referenceProfile 3)] (referenceChannelsOpen 3)
      true false (0, 0) (1, 0) = 0 := by
  exact diagonalModulated_transition_zero referenceParameters referenceScatteringParameters
    [referenceProfile 3] (referenceChannelsOpen 3) true false (0, 0) (1, 0) (by norm_num)

end RealizedExamples
/-!
## 主要定理の検査

以下は既に証明した定理の公理依存を表示するコマンドであり、新しい公理の宣言ではない。
-/

#print axioms channelSymmetry_commutes_waveNumber
#print axioms scatteringSolution_equivariant
#print axioms scatteringMatrix_commutes
#print axioms scatteringSymmetry_commutes_weightRoot
#print axioms fluxNormalizedScatteringMatrix_commutes
#print axioms scattering_symmetry_form_conserved
#print axioms scattering_symmetry_pairing_conserved
#print axioms unitary_eigenvalue_phase
#print axioms scattering_eigenvalue_transition_zero
#print axioms scattering_entry_zero_of_diagonalSymmetry
#print axioms firstModulated_symmetry
#print axioms diagonalModulated_symmetry
#print axioms fourierMode_normalized
#print axioms fourierMode_mass_eigenvector
#print axioms channelMode_normalized
#print axioms firstModulated_transition_zero
#print axioms diagonalModulated_transition_zero
#print axioms scatteringField_frequencyEigenvector
#print axioms scattering_timeTranslation_covariance
#print axioms referenceChannelsOpen
#print axioms referenceFirst_forbidden_transition
#print axioms referenceDiagonal_forbidden_transition

end InternalSymmetry
end TwelveDimensionalPhaseSpace
