import Bilevel.PolishedLiteralRawColumns
import Bilevel.ParametricGradientMeasurable

/-! Joint continuity of the literal disclosed scalar formulas in arbitrary
raw column arrays and query variables. No hidden frame completion occurs. -/
noncomputable section
set_option maxHeartbeats 1800000
open scoped BigOperators
namespace Bilevel.PolishedLiteral.Parameters
open PrimitiveGeometry ChiBoundedChain ChiPrefixEvaluation RadialWrapper
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))
variable {T : Type*} [TopologicalSpace T]

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawSelector_continuous (r : ℕ) (i : Fin (P.macroNode.n+1))
    (a : T → P.MacroColumns) (x : T → X) (ha : Continuous a) (hx : Continuous x) :
    Continuous (fun t => P.rawSelector r (a t) i (x t)) :=
  (selector_contDiff P.macroNode.n 3 i).continuous.comp
    (((readout_continuous P.macroNode.n r P.macroNode.radius).comp (ha.prodMk hx)).const_smul P.macroNode.width⁻¹)

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawMicro_continuous (counts : Fin (P.macroNode.n+1) → ℕ) (i : Fin (P.macroNode.n+1))
    (b : T → P.MicroColumns) (u : T → U) (hb : Continuous b) (hu : Continuous u) :
    Continuous (fun t => P.rawMicro counts (b t) i (u t)) :=
  (readout_continuous P.n (counts i) P.radius).comp
    (((continuous_apply i).comp hb).prodMk hu)

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawSelectedFlat_continuous (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (a : T → P.MacroColumns) (b : T → P.MicroColumns) (x : T → X) (u : T → U)
    (ha : Continuous a) (hb : Continuous b) (hx : Continuous x) (hu : Continuous u) :
    Continuous (fun t => P.rawSelectedFlat r counts (a t) (b t) τ (pack (x t) (u t))) := by
  unfold rawSelectedFlat
  apply continuous_finset_sum
  intro i _
  exact (P.rawSelector_continuous r i a x ha hx).mul
    ((flatResidual_contDiff P.n P.L P.β τ).continuous.comp (P.rawMicro_continuous counts i b u hb hu))

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawSelectedInactive_continuous (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ) (j : ℕ)
    (a : T → P.MacroColumns) (b : T → P.MicroColumns) (x : T → X) (u : T → U)
    (ha : Continuous a) (hb : Continuous b) (hx : Continuous x) (hu : Continuous u) :
    Continuous (fun t => P.rawSelectedInactive r counts (a t) (b t) τ j (pack (x t) (u t))) := by
  unfold rawSelectedInactive
  apply continuous_finset_sum
  intro i _
  exact (P.rawSelector_continuous r i a x ha hx).mul
    ((inactivePiece_contDiff P.n P.J P.L P.β P.δ τ j).continuous.comp (P.rawMicro_continuous counts i b u hb hu))

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawSelectedResidual_continuous (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ)
    (a : T → P.MacroColumns) (b : T → P.MicroColumns) (x : T → X) (u : T → U)
    (ha : Continuous a) (hb : Continuous b) (hx : Continuous x) (hu : Continuous u) :
    Continuous (fun t => P.rawSelectedResidual r counts (a t) (b t) (pack (x t) (u t))) := by
  unfold rawSelectedResidual
  apply continuous_finset_sum
  intro i _
  exact (P.rawSelector_continuous r i a x ha hx).mul
    ((residual_contDiff P.n 3 P.L P.β).continuous.comp (P.rawMicro_continuous (P.activeCutCounts r counts) i b u hb hu))

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawSelectedPiece_continuous (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (j : ℕ)
    (a : T → P.MacroColumns) (b : T → P.MicroColumns) (x : T → X) (u : T → U)
    (ha : Continuous a) (hb : Continuous b) (hx : Continuous x) (hu : Continuous u) :
    Continuous (fun t => P.rawSelectedPiece r counts (a t) (b t) j (pack (x t) (u t))) := by
  unfold rawSelectedPiece
  apply continuous_finset_sum
  intro i _
  exact (P.rawSelector_continuous r i a x ha hx).mul
    ((piece_contDiff P.n P.J P.L P.β P.δ j).continuous.comp (P.rawMicro_continuous (P.activeCutCounts r counts) i b u hb hu))

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawInactiveLower_continuous (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ)
    (a : T → P.MacroColumns) (b : T → P.MicroColumns) (q : T → FullMeanSpace (X:=X) (U:=U))
    (ha : Continuous a) (hb : Continuous b) (hq : Continuous q) :
    Continuous (fun t => P.rawInactiveLower r counts (a t) (b t) τ (q t)) := by
  have hx : Continuous (fun t => (q t).fst.fst) :=
    (fstMap (X:=X) (U:=U)).continuous.comp ((fstMap (X:=Joint X U) (U:=Joint U ℝ)).continuous.comp hq)
  have hu : Continuous (fun t => (q t).snd.fst) :=
    (fstMap (X:=U) (U:=ℝ)).continuous.comp ((sndMap (X:=Joint X U) (U:=Joint U ℝ)).continuous.comp hq)
  have hs : Continuous (fun t => (q t).snd.snd) :=
    (sndMap (X:=U) (U:=ℝ)).continuous.comp ((sndMap (X:=Joint X U) (U:=Joint U ℝ)).continuous.comp hq)
  have hsum : Continuous (fun t => ∑ j ∈ Finset.range (P.J+1),
      P.rawSelectedInactive r counts (a t) (b t) τ j (pack (q t).fst.fst (q t).snd.fst)*
        PolishedLiteralCompensated.normal (P.w j) (q t).snd.snd) := by
    apply continuous_finset_sum
    intro j _
    exact (P.rawSelectedInactive_continuous r counts τ j a b _ _ ha hb hx hu).mul
      ((PolishedLiteral.normalAtWidth_contDiff (P.w j) (k:=3)).continuous.comp hs)
  exact (((PolishedLiteral.lowerBase_contDiff P.μ P.L).continuous.comp hq).add
    (continuous_const.mul ((P.rawSelectedFlat_continuous r counts τ a b _ _ ha hb hx hu).pow 2))).sub
      (continuous_const.mul hsum)

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawActiveLower_continuous (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ)
    (a : T → P.MacroColumns) (b : T → P.MicroColumns) (q : T → FullMeanSpace (X:=X) (U:=U))
    (ha : Continuous a) (hb : Continuous b) (hq : Continuous q) :
    Continuous (fun t => P.rawActiveLower r counts (a t) (b t) (q t)) := by
  have hx : Continuous (fun t => (q t).fst.fst) :=
    (fstMap (X:=X) (U:=U)).continuous.comp ((fstMap (X:=Joint X U) (U:=Joint U ℝ)).continuous.comp hq)
  have hu : Continuous (fun t => (q t).snd.fst) :=
    (fstMap (X:=U) (U:=ℝ)).continuous.comp ((sndMap (X:=Joint X U) (U:=Joint U ℝ)).continuous.comp hq)
  have hs : Continuous (fun t => (q t).snd.snd) :=
    (sndMap (X:=U) (U:=ℝ)).continuous.comp ((sndMap (X:=Joint X U) (U:=Joint U ℝ)).continuous.comp hq)
  have hsum : Continuous (fun t => ∑ j ∈ Finset.range (P.J+1),
      P.rawSelectedPiece r counts (a t) (b t) j (pack (q t).fst.fst (q t).snd.fst)*
        PolishedLiteralCompensated.normal (P.w j) (q t).snd.snd) := by
    apply continuous_finset_sum
    intro j _
    exact (P.rawSelectedPiece_continuous r counts j a b _ _ ha hb hx hu).mul
      ((PolishedLiteral.normalAtWidth_contDiff (P.w j) (k:=3)).continuous.comp hs)
  exact (((PolishedLiteral.lowerBase_contDiff P.μ P.L).continuous.comp hq).add
    (continuous_const.mul ((P.rawSelectedResidual_continuous r counts a b _ _ ha hb hx hu).pow 2))).sub
      (continuous_const.mul hsum)

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawRelease_continuous (counts : Fin (P.macroNode.n+1) → ℕ) (i : Fin (P.macroNode.n+1))
    (b : T → P.MicroColumns) (u : T → U) (hb : Continuous b) (hu : Continuous u) :
    Continuous (fun t => P.rawRelease counts (b t) i (u t)) :=
  (releaseGate_contDiff (k:=3)).continuous.comp
    (((EuclideanSpace.proj (𝕜:=ℝ) (Fin.last P.n)).continuous.comp
      (P.rawMicro_continuous counts i b u hb hu)).div_const P.macroNode.width)

omit [CompleteSpace X] [CompleteSpace U] in
theorem rawExactUpper_continuous (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ)
    (a : T → P.MacroColumns) (b : T → P.MicroColumns) (q : T → FullMeanSpace (X:=X) (U:=U))
    (ha : Continuous a) (hb : Continuous b) (hq : Continuous q) :
    Continuous (fun t => P.rawExactUpper r counts (a t) (b t) (q t)) := by
  have hx : Continuous (fun t => (q t).fst.fst) :=
    (fstMap (X:=X) (U:=U)).continuous.comp ((fstMap (X:=Joint X U) (U:=Joint U ℝ)).continuous.comp hq)
  have hu : Continuous (fun t => (q t).snd.fst) :=
    (fstMap (X:=U) (U:=ℝ)).continuous.comp ((sndMap (X:=Joint X U) (U:=Joint U ℝ)).continuous.comp hq)
  have hs : Continuous (fun t => (q t).snd.snd) :=
    (sndMap (X:=U) (U:=ℝ)).continuous.comp ((sndMap (X:=Joint X U) (U:=Joint U ℝ)).continuous.comp hq)
  have hz := ((readout_continuous P.macroNode.n r P.macroNode.radius).comp (ha.prodMk hx)).const_smul P.macroNode.width⁻¹
  have hc : Continuous (fun t => closedChain P.macroNode.n P.macroNode.ell P.macroNode.width
      (fun i => P.rawRelease counts (b t) i (q t).snd.fst)
      (readout P.macroNode.n r P.macroNode.radius (a t) (q t).fst.fst)) := by
    unfold closedChain closedValue
    apply continuous_const.mul
    apply Continuous.add ((PolishedLiteral.value_contDiff P.macroNode.n 3).continuous.comp hz)
    apply continuous_finset_sum
    intro i _
    exact ((residualTerm_contDiff P.macroNode.n 3 i).continuous.comp hz).mul
      ((P.rawRelease_continuous counts i b _ hb hu).sub continuous_const)
  have hsum : Continuous (fun t => ∑ i : Fin (P.macroNode.n+1),P.rawSelector r (a t) i (q t).fst.fst*
      microClosedCarrier P.n P.L P.β P.receiver P.ν P.force P.macroNode.width
        (P.rawMicro counts (b t) i (q t).snd.fst)) := by
    apply continuous_finset_sum
    intro i _
    exact (P.rawSelector_continuous r i a _ ha hx).mul
      ((microClosedCarrier_contDiff P.n P.L P.β P.receiver P.ν P.force P.macroNode.width).continuous.comp
        (P.rawMicro_continuous counts i b _ hb hu))
  exact (((hc.add ((ChiRecursive.full_bowl_contDiff P.macroRadial P.macroNode.radius 3).continuous.comp hx)).add
    ((ChiRecursive.full_bowl_contDiff P.ν P.radius 3).continuous.comp hu)).add hsum).add
      (continuous_const.mul hs)

end Bilevel.PolishedLiteral.Parameters
