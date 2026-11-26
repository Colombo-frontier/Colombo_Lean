import Bilevel.TransportNetworkObservation
import Bilevel.TransportNetworkQueryMoment
import Bilevel.ProjectionQuery

/-! Finite adaptive observation procedures on the actual fixed latent network.
Every continuation may depend on the observed answer. Forward/reverse actions
use the same edge variable; no independent resampling is introduced. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace Bilevel.TransportNetwork
open EuclideanGaussian

inductive Protocol (n d T : ℕ) : ℕ → Type
  | halt {m : ℕ} : Protocol n d T m
  | query {m : ℕ} (v : Vertex n) (q : Space d)
      (next : (Fin T → ℝ) → Protocol n d T m) : Protocol n d T (m+1)
  | named {m : ℕ} (v : Vertex n) (i : Fin T)
      (next : Space d → Protocol n d T m) : Protocol n d T (m+1)
  | forward {m : ℕ} (e : Edge n) (q : Space d)
      (next : Space d → Protocol n d T m) : Protocol n d T (m+1)
  | reverse {m : ℕ} (e : Edge n) (q : Space d)
      (next : Space d → Protocol n d T m) : Protocol n d T (m+1)

def queryBad {n d T : ℕ} (hT : T ≤ d) (a : ℝ) :
    {m : ℕ} → Protocol n d T m → Latent n d → Prop
  | _,.halt,_ => False
  | _,.query v q next,z => (a < ∑ i, ⟪q,frame T hT z v i⟫^2) ∨
      queryBad hT a (next (queryObservation T hT v q z)) z
  | _,.named v i next,z => queryBad hT a (next (namedObservation T hT v i z)) z
  | _,.forward e q next,z => queryBad hT a (next (forwardObservation e q z)) z
  | _,.reverse e q next,z => queryBad hT a (next (reverseObservation e q z)) z

/-- The joint observation/latent event must be Borel. This is a regularity
condition on the chosen adaptive continuations, not a probability bound. -/
def Regular {n d T : ℕ} (hT : T ≤ d) (a : ℝ) :
    {m : ℕ} → Protocol n d T m → Prop
  | _,.halt => True
  | _,.query _ _ next =>
      MeasurableSet {p : (Fin T → ℝ) × Latent n d | queryBad hT a (next p.1) p.2} ∧
      ∀ y, Regular hT a (next y)
  | _,.named _ _ next | _,.forward _ _ next | _,.reverse _ _ next =>
      MeasurableSet {p : Space d × Latent n d | queryBad hT a (next p.1) p.2} ∧
      ∀ y, Regular hT a (next y)

/-- Query nodes are the normalized residual innovations. Edge nodes can only
act on vectors already in their actual input known spaces. -/
def Valid {n d T : ℕ} : {m : ℕ} → Protocol n d T m → Known n d → Prop
  | _,.halt,_ => True
  | _,.query v q next,W => q ∈ (W v)ᗮ ∧ ‖q‖ = 1 ∧
      ∀ y, Valid (next y) (insert W v q)
  | _,.named v _ next,W => ∀ y, Valid (next y) (insert W v y)
  | _,.forward e q next,W => q ∈ W (src e) ∧
      ∀ y, Valid (next y) (insert W (dst e) y)
  | _,.reverse e q next,W => q ∈ W (dst e) ∧
      ∀ y, Valid (next y) (insert W (src e) y)

def finalKnown {n d T : ℕ} (hT : T ≤ d) :
    {m : ℕ} → Protocol n d T m → Known n d → Latent n d → Known n d
  | _,.halt,W,_ => W
  | _,.query v q next,W,z => finalKnown hT (next (queryObservation T hT v q z)) (insert W v q) z
  | _,.named v i next,W,z =>
      let y := namedObservation T hT v i z
      finalKnown hT (next y) (insert W v y) z
  | _,.forward e q next,W,z =>
      let y := forwardObservation e q z
      finalKnown hT (next y) (insert W (dst e) y) z
  | _,.reverse e q next,W,z =>
      let y := reverseObservation e q z
      finalKnown hT (next y) (insert W (src e) y) z

theorem queryBad_measurable {n d T m : ℕ} (hT : T ≤ d) (a : ℝ)
    (P : Protocol n d T m) (hP : Regular hT a P) :
    MeasurableSet {z | queryBad hT a P z} := by
  cases P with
  | halt => exact MeasurableSet.empty
  | query v q next =>
    have hm : Measurable (fun z : Latent n d => ∑ i, ⟪q,frame T hT z v i⟫^2) :=
      Finset.measurable_sum _ (fun i _ =>
        (((continuous_const.inner continuous_id).measurable.comp
          (frame_coordinate_measurable n d T hT v i)).pow_const 2))
    exact (measurableSet_lt measurable_const hm).union
      ((query_measurable T hT v q).prodMk measurable_id hP.1)
  | named v i next => exact ((named_measurable T hT v i).prodMk measurable_id) hP.1
  | forward e q next => exact ((forward_measurable e q).prodMk measurable_id) hP.1
  | reverse e q next => exact ((reverse_measurable e q).prodMk measurable_id) hP.1

def DimensionBound {n D : ℕ} (W : Known n D) (d : ℕ) : Prop :=
  ∀ v, Module.finrank ℝ (W v) ≤ d

theorem dimensionBound_insert {n D d : ℕ} {W : Known n D} (hW : DimensionBound W d)
    (v : Vertex n) (q : Space D) : DimensionBound (insert W v q) (d+1) := by
  intro j
  by_cases h : j = v
  · subst j
    have he : insert W v q v = W v ⊔ Submodule.span ℝ {q} := Function.update_self _ _ _
    rw [he]
    exact (ProjectionQuery.finrank_insert_le (W v) q).trans (Nat.add_le_add_right (hW v) 1)
  · have he : insert W v q j = W j := Function.update_of_ne h _ _
    rw [he]
    exact (hW j).trans (Nat.le_succ d)

theorem finalKnown_dimension {n D T m d : ℕ} (hT : T ≤ D)
    (P : Protocol n D T m) (W : Known n D) (hW : DimensionBound W d) (z : Latent n D) :
    DimensionBound (finalKnown hT P W z) (d+m) := by
  induction P generalizing W d with
  | halt => exact fun v => (hW v).trans (Nat.le_add_right d _)
  | query v q next ih =>
    simpa only [finalKnown,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      ih (queryObservation T hT v q z) (insert W v q) (dimensionBound_insert hW v q)
  | named v i next ih =>
    simpa only [finalKnown,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      ih (namedObservation T hT v i z) (insert W v _) (dimensionBound_insert hW v _)
  | forward e q next ih =>
    simpa only [finalKnown,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      ih (forwardObservation e q z) (insert W (dst e) _) (dimensionBound_insert hW (dst e) _)
  | reverse e q next ih =>
    simpa only [finalKnown,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      ih (reverseObservation e q z) (insert W (src e) _) (dimensionBound_insert hW (src e) _)

end Bilevel.TransportNetwork
