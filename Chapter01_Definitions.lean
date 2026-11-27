import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# 第一章　定義・仮定・証明範囲

十二次元相空間から動機づけられた有限内部格子模型の共通定義。

## このファイルが行うこと

1. 連続相空間の座標と P_a = -E_a という符号規約を固定する。
2. 内部格子、有限成分、正定値内積を持つヒルベルト空間を指定する。
3. パラメータ、シフト、質量二乗行列、相互作用の条件を定義する。
4. 線形安定性、静的散乱、選択則で使う仮定を別々に記述する。
5. 参照パラメータと零ポテンシャルが所定の条件を満たすことを証明する。

## このファイルではまだ証明しないこと

正準2形式の非退化性、ポアソン括弧のJacobi恒等式、
格子ラプラシアンのスペクトル上界、質量二乗行列の正の下界、
場の解の存在・一意性、線形安定性、散乱行列の存在・ユニタリティ。
これらは後続章の定理であり、ここで未証明の公理として導入しない。

有限内部成分の導入は外部空間まで有限化する操作ではない。
連続12次元粒子模型から有限格子場への移行には模型化の選択が含まれる。

## 使用方法

mathlibを導入したLean 4プロジェクトにこのファイルを配置し、
そのプロジェクトで次を実行する。

    lake env lean -DwarningAsError=true Chapter01_Definitions.lean

## 検証記録

Lean 4.24.0 / mathlib v4.24.0でコンパイル確認済み。
mathlibのコミット：f897ebcf72cd16f89ab4577d0c826cd14afaafc7
警告をエラーとして扱う上記コマンドで、終了コード0。
末尾で確認する補助定理の公理依存は
propext、Classical.choice、Quot.soundのみ。
他の版で利用する場合には、その版でも改めてビルドする。
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace TwelveDimensionalPhaseSpace

/-! ## 1.1　連続座標と有限内部状態 -/

abbrev SpatialIndex := Fin 3
abbrev TemporalIndex := Fin 3
abbrev SpaceCoordinates := SpatialIndex → ℝ
abbrev TimeCoordinates := TemporalIndex → ℝ
abbrev SpatialMomenta := SpatialIndex → ℝ
abbrev TemporalMomenta := TemporalIndex → ℝ

/-- q=(x,t), p=(p,P) の12個の実座標。正準形式は第二章で構成する。 -/
abbrev PhasePoint :=
  (SpaceCoordinates × TimeCoordinates) ×
    (SpatialMomenta × TemporalMomenta)

/-- 時間座標に対応する共役運動量は P_a=-E_a とする。 -/
def temporalEnergy (z : PhasePoint) (a : TemporalIndex) : ℝ :=
  -z.2.2 a

theorem temporalMomentum_eq_neg_energy (z : PhasePoint) (a : TemporalIndex) :
    z.2.2 a = -temporalEnergy z a := by
  simp [temporalEnergy]

/-- 型として定義した連続相空間の実ベクトル空間次元。 -/
theorem phasePoint_finrank : Module.finrank ℝ PhasePoint = 12 := by
  simp [PhasePoint, SpaceCoordinates, TimeCoordinates,
    SpatialMomenta, TemporalMomenta, SpatialIndex, TemporalIndex]

abbrev ObservedTime := ℝ
abbrev SpatialPosition := SpaceCoordinates
abbrev TransverseMomentum := Fin 2 → ℝ

/--
周期格子の添字。
以下の有限模型では [NeZero N] を要求する。自然数NについてこれはN≥1に相当する。
N=0の場合のZModは無限なので、有限模型の範囲から除く。
-/
abbrev Grid (N : ℕ) := ZMod N × ZMod N

/-- 行列計算に用いる成分表示。 -/
abbrev InternalVector (N : ℕ) := Grid N → ℂ

/--
通常の正定値ℓ²内積を持つヒルベルト空間。
単なる関数型のノルムを自動的にℓ²ノルムとみなさないため、別の型で明示する。
-/
abbrev InternalHilbert (N : ℕ) [NeZero N] :=
  EuclideanSpace ℂ (Grid N)

abbrev InternalMatrix (N : ℕ) := Matrix (Grid N) (Grid N) ℂ

/-- 外部空間は連続のままの、有限内部成分を持つ場。 -/
abbrev CoordinateField (N : ℕ) :=
  ObservedTime → SpatialPosition → InternalVector N

abbrev HilbertField (N : ℕ) [NeZero N] :=
  ObservedTime → SpatialPosition → InternalHilbert N

/-- 一般の時間依存を許した行列値ポテンシャル。静的条件は別に課す。 -/
abbrev Potential (N : ℕ) :=
  ObservedTime → SpatialPosition → InternalMatrix N

/-! ## 1.2　パラメータと仮定の台帳 -/

/--
模型の実数パラメータ。
vMinはポテンシャルの下界候補であり、実際の下界条件は後で別に要求する。
massParameterの符号は制限せず、その二乗を質量二乗式に用いる。
-/
structure ModelParameters where
  latticeSpacing : ℝ
  massParameter : ℝ
  vMin : ℝ
  latticeSpacing_pos : 0 < latticeSpacing

/-- 格子作用素の上界から導く予定の、質量二乗の十分条件に現れる量。 -/
def sufficientMassGap (p : ModelParameters) : ℝ :=
  p.massParameter ^ 2 + p.vMin - 8 / p.latticeSpacing ^ 2

def PositiveGapCondition (p : ModelParameters) : Prop :=
  0 < sufficientMassGap p

/-- 通常の正定値内積に関する、有限正方行列のユニタリ性。 -/
def IsUnitaryMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

section FiniteModel

variable {N : ℕ} [NeZero N]

/-- 実数rに対応するスカラー行列rI。 -/
def realScalarMatrix (r : ℝ) : InternalMatrix N :=
  (r : ℂ) • (1 : InternalMatrix N)

/-- Loewner順序によるA≥rI。複素数の成分ごとの大小比較ではない。 -/
def HasMatrixLowerBound (A : InternalMatrix N) (r : ℝ) : Prop :=
  (A - realScalarMatrix r).PosSemidef

/--
二方向のシフトに要求する抽象的な代数条件。
具体的な一格子並進行列と、これらの条件の証明は第四章で構成する。
この抽象条件だけでは表現の忠実性や非自明性まで要求していない。
-/
structure InternalShifts (N : ℕ) [NeZero N] where
  first : InternalMatrix N
  second : InternalMatrix N
  first_unitary : IsUnitaryMatrix first
  second_unitary : IsUnitaryMatrix second
  first_periodic : first ^ N = 1
  second_periodic : second ^ N = 1
  commute : first * second = second * first

/-- 二方向・最近接差分を採用した内部ラプラシアン。 -/
def internalLaplacian (p : ModelParameters) (s : InternalShifts N) :
    InternalMatrix N :=
  (p.latticeSpacing ^ 2)⁻¹ •
    (((2 : ℂ) • (1 : InternalMatrix N) - s.first - s.first.conjTranspose) +
      ((2 : ℂ) • (1 : InternalMatrix N) - s.second - s.second.conjTranspose))

/-- 障壁外で使う自由質量二乗行列。定義自体では正値性を仮定しない。 -/
def freeMassSquared (p : ModelParameters) (s : InternalShifts N) :
    InternalMatrix N :=
  realScalarMatrix (p.massParameter ^ 2) - internalLaplacian p s

/-- 一般の相互作用付き質量二乗行列。 -/
def massSquared (p : ModelParameters) (s : InternalShifts N)
    (V : Potential N) (τ : ObservedTime) (x : SpatialPosition) :
    InternalMatrix N :=
  freeMassSquared p s + V τ x

def IsHermitianPotential (V : Potential N) : Prop :=
  ∀ τ x, (V τ x).IsHermitian

/-- τに明示的に依存しないことを、時刻0での値との一致で表す。 -/
def IsStaticPotential (V : Potential N) : Prop :=
  ∀ τ x, V τ x = V 0 x

def HasUniformPotentialLowerBound (V : Potential N) (vMin : ℝ) : Prop :=
  ∀ τ x, HasMatrixLowerBound (V τ x) vMin

/--
全成分についての一様有界性。
固定された有限内部次元では、作用素ノルムの有界性へ接続できる条件である。
その接続と外部空間上の作用素の定義域は、第七章で扱う。
-/
def IsUniformlyBoundedPotential (V : Potential N) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ τ x i j, ‖V τ x i j‖ ≤ C

/--
後続の線形安定性定理へ渡す条件。
安定性そのものや、質量行列の下界を結論として先取りしない。
運動項は通常の正の内積を用いた標準形として、場の作用を定義する章で固定する。
解の正則性・関数空間・境界条件は、第七章の定理で追加する。
-/
structure StabilityHypotheses (p : ModelParameters) (V : Potential N) : Prop where
  hermitian : IsHermitianPotential V
  static : IsStaticPotential V
  uniformlyBounded : IsUniformlyBoundedPotential V
  lowerBound : HasUniformPotentialLowerBound V p.vMin
  positiveGap : PositiveGapCondition p

/--
静的散乱の係数に使う条件。質量二乗の正値性とは独立に記述する。
局所的なWronskian流束保存では、このうち自己共役性を直接使う。
-/
structure StaticFluxHypotheses (V : Potential N) : Prop where
  hermitian : IsHermitianPotential V
  static : IsStaticPotential V

/-- 既に得た仮定のうち、静的流束の議論に必要な部分だけを取り出す。 -/
def StabilityHypotheses.toStaticFluxHypotheses
    {p : ModelParameters} {V : Potential N} (h : StabilityHypotheses p V) :
    StaticFluxHypotheses V :=
  ⟨h.hermitian, h.static⟩

/-! ### 静的な有限幅障壁と開チャネル -/

/-- 有限幅を持つ自己共役な定数行列障壁の一層。 -/
structure BarrierLayer (N : ℕ) [NeZero N] where
  width : ℝ
  width_pos : 0 < width
  value : InternalMatrix N
  hermitian : value.IsHermitian

/--
有限個の層をx=0から順に並べたポテンシャル。
各区間は左端を含み右端を含まない。全層の外側では0とする。
接続点での解と導関数の条件は、散乱問題を定義する章で課す。
-/
def layeredPotential : List (BarrierLayer N) → ℝ → InternalMatrix N
  | [], _ => 0
  | layer :: rest, x =>
      if x < 0 then 0
      else if x < layer.width then layer.value
      else layeredPotential rest (x - layer.width)

/--
外部の第一方向だけに依存する有限層障壁であること。
存在を要求する対象は具体的な有限リストであり、未知の保存則ではない。
-/
def HasLayeredRepresentation (V : Potential N) : Prop :=
  ∃ layers : List (BarrierLayer N),
    ∀ τ x, V τ x = layeredPotential layers (x 0)

theorem static_of_layeredRepresentation {V : Potential N}
    (h : HasLayeredRepresentation V) : IsStaticPotential V := by
  rcases h with ⟨layers, h⟩
  intro τ x
  exact (h τ x).trans (h 0 x).symm

structure ScatteringParameters where
  frequency : ℝ
  frequency_pos : 0 < frequency
  transverseMomentum : TransverseMomentum

/-- Ω²=ω²-|k_perp|²。外部一方向の定常散乱方程式で用いる。 -/
def reducedFrequencySquared (k : ScatteringParameters) : ℝ :=
  k.frequency ^ 2 -
    (k.transverseMomentum 0 ^ 2 + k.transverseMomentum 1 ^ 2)

/--
Ω²I-M₀²の正定値性。外部で全波数が厳密に正になる条件に対応する。
固有値表示との同値性は、チャネルを構成する後続章で証明する。
障壁内部まで全チャネルが開いていることは要求しない。
-/
def AllExteriorChannelsOpen (p : ModelParameters) (s : InternalShifts N)
    (k : ScatteringParameters) : Prop :=
  (realScalarMatrix (reducedFrequencySquared k) - freeMassSquared p s).PosDef

/--
最初の散乱定理で扱う、全外部チャネルが開いた有限層障壁の条件。
静的条件はlayeredから得られるので、重複して要求しない。
散乱解の存在、一意性、ユニタリティはいずれも仮定に含まれない。
-/
structure ScatteringHypotheses (p : ModelParameters) (s : InternalShifts N)
    (V : Potential N) (k : ScatteringParameters) : Prop where
  hermitian : IsHermitianPotential V
  layered : HasLayeredRepresentation V
  allExteriorChannelsOpen : AllExteriorChannelsOpen p s k

def ScatteringHypotheses.toStaticFluxHypotheses
    {p : ModelParameters} {s : InternalShifts N}
    {V : Potential N} {k : ScatteringParameters}
    (h : ScatteringHypotheses p s V k) : StaticFluxHypotheses V :=
  ⟨h.hermitian, static_of_layeredRepresentation h.layered⟩

/-! ### 残存する内部対称性 -/

/--
選択則の定理に渡す条件。
Qは自由質量行列と相互作用の双方に対称性を持つ。
散乱行列との可換性や禁止遷移は、ここで仮定せず後続章で導く。
-/
structure SymmetryHypotheses (p : ModelParameters) (s : InternalShifts N)
    (V : Potential N) (Q : InternalMatrix N) : Prop where
  unitary : IsUnitaryMatrix Q
  freeCommute : Q * freeMassSquared p s = freeMassSquared p s * Q
  interactionCommute : ∀ τ x, Q * V τ x = V τ x * Q

/-- 左右両側の外部チャネル。方向と内部格子ラベルを保持する。 -/
abbrev ScatteringChannel (N : ℕ) := Sum (Grid N) (Grid N)

abbrev ScatteringMatrix (N : ℕ) :=
  Matrix (ScatteringChannel N) (ScatteringChannel N) ℂ

/--
流束規格化した行列に対する、将来のユニタリティ定理の結論。
これは性質の定義であり、構成前の散乱行列がこの性質を持つとは主張しない。
-/
def IsFluxUnitary (SF : ScatteringMatrix N) : Prop :=
  IsUnitaryMatrix SF

/-! ## 1.3　仮定を実現する参照データと、証明範囲 -/

def referenceParameters : ModelParameters where
  latticeSpacing := 3
  massParameter := 1
  vMin := 0
  latticeSpacing_pos := by norm_num

theorem referenceParameters_gap :
    sufficientMassGap referenceParameters = 1 / 9 := by
  norm_num [sufficientMassGap, referenceParameters]

theorem referenceParameters_positiveGap :
    PositiveGapCondition referenceParameters := by
  norm_num [PositiveGapCondition, sufficientMassGap, referenceParameters]

def zeroPotential : Potential N :=
  fun _ _ => 0

/--
参照パラメータと零ポテンシャルが、安定性定理への入力条件を満たす。
これは安定性そのものの証明ではない。任意のシフトを含む質量行列の
正の下界を導くには、第四・第五章の格子評価がさらに必要である。
-/
theorem reference_zero_stabilityHypotheses :
    StabilityHypotheses referenceParameters (zeroPotential : Potential N) := by
  constructor
  · intro τ x
    exact (Matrix.PosSemidef.zero :
      (0 : InternalMatrix N).PosSemidef).isHermitian
  · intro τ x
    rfl
  · refine ⟨0, le_rfl, ?_⟩
    intro τ x i j
    simp [zeroPotential]
  · intro τ x
    simpa [HasMatrixLowerBound, zeroPotential, referenceParameters,
      realScalarMatrix] using
      (Matrix.PosSemidef.zero : (0 : InternalMatrix N).PosSemidef)
  · exact referenceParameters_positiveGap

theorem zeroPotential_layered :
    HasLayeredRepresentation (zeroPotential : Potential N) := by
  refine ⟨[], ?_⟩
  intro τ x
  rfl

end FiniteModel

/-!
## 証明範囲の確認

この章の実際の定理：

* temporalMomentum_eq_neg_energy：時間共役量の符号規約。
* phasePoint_finrank：定義した実相空間の次元。
* static_of_layeredRepresentation：有限層表示から静的条件への含意。
* referenceParameters_gap / referenceParameters_positiveGap：参照値の計算。
* reference_zero_stabilityHypotheses：参照データが入力条件を満たすこと。
* zeroPotential_layered：零相互作用の有限層表示。

後続章に残る条件：

* 正準形式、ポアソン括弧、質量殻制約の力学。
* 巡回置換から構成したシフトがInternalShiftsの条件を満たすこと。
* 内部ラプラシアンの正値性・上界と、質量行列の正の下界。
* 場の作用、正の運動項、解の正則性、関数空間と境界条件。
* 場の解と散乱解の存在・一意性、保存則、ユニタリティ、選択則。

初期の対象範囲：

静的な線形模型における有限エネルギー解のエネルギー評価、
有限層障壁を持つ全開チャネル散乱、残存内部対称性に対応する選択則。
独立した三つの物理時計、非線形安定性、連続極限、完全な量子場理論の
S行列、および追加時間を識別する新しい観測予測は別の研究課題である。
-/

-- この章の補助定理について、依存する公理を表示する。
#print axioms phasePoint_finrank
#print axioms referenceParameters_gap
#print axioms reference_zero_stabilityHypotheses

end TwelveDimensionalPhaseSpace
