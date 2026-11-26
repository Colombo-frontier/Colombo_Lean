import NCConcave16991.Smoothness
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The mathematical problem and unrestricted finite-budget oracle policies

This is the Section 2 model. Component gradients are derivatives of actual
functions on an open neighborhood. The joint space uses the Euclidean `L²`
product norm. The value function is the supremum of the actual component
average, and is proved to attain its maximum on the known dual domain.

Policies see the entire query/answer history and a private seed. They can repeat
queries, stop early, and return any primal point. The recursion has a fixed
deterministic fuel bound. No oracle-complexity bound is postulated here.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace NCConcave16991

noncomputable section

abbrev PrimalSpace (dx : ℕ) := EuclideanSpace ℝ (Fin dx)
abbrev DualSpace (dy : ℕ) := EuclideanSpace ℝ (Fin dy)
abbrev JointSpace (dx dy : ℕ) := WithLp 2 (PrimalSpace dx × DualSpace dy)

def jointPoint {dx dy : ℕ} (x : PrimalSpace dx) (y : DualSpace dy) : JointSpace dx dy :=
  WithLp.toLp 2 (x, y)

/-- The product really uses the sum of squared Euclidean norms. -/
theorem joint_difference_norm_sq {dx dy : ℕ} (z z' : JointSpace dx dy) :
    ‖z - z'‖ ^ 2 = ‖z.fst - z'.fst‖ ^ 2 + ‖z.snd - z'.snd‖ ^ 2 := by
  simpa using WithLp.prod_norm_sq_eq_of_L2 (z - z')

structure ProblemParameters where
  n : ℕ
  n_pos : 0 < n
  L : ℝ
  L_pos : 0 < L
  gap : ℝ
  gap_pos : 0 < gap
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  diameter : ℝ
  diameter_nonneg : 0 ≤ diameter

/-- This information is known to the algorithm; the component functions are not. -/
structure KnownDualDomain (dy : ℕ) (D : ℝ) where
  carrier : Set (DualSpace dy)
  nonempty : carrier.Nonempty
  compact : IsCompact carrier
  convex : Convex ℝ carrier
  diameter_bound : ∀ y ∈ carrier, ∀ y' ∈ carrier, ‖y - y'‖ ≤ D

def productDomain {dy : ℕ} {D : ℝ} (dx : ℕ) (K : KnownDualDomain dy D) :
    Set (JointSpace dx dy) := {z | z.snd ∈ K.carrier}

def componentAverage {n dx dy : ℕ} (f : Fin n → JointSpace dx dy → ℝ)
    (z : JointSpace dx dy) : ℝ := (n : ℝ)⁻¹ * ∑ i, f i z

def primalObjective {n dx dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D)
    (f : Fin n → JointSpace dx dy → ℝ) (x : PrimalSpace dx) : ℝ :=
  sSup ((fun y => componentAverage f (jointPoint x y)) '' K.carrier)

/-- All analytic assumptions of Section 2, apart from the selected IS/AS class. -/
structure Problem (p : ProblemParameters) (dx dy : ℕ)
    (K : KnownDualDomain dy p.diameter) where
  component : Fin p.n → JointSpace dx dy → ℝ
  componentGradient : Fin p.n → JointSpace dx dy → JointSpace dx dy
  neighborhood : Set (JointSpace dx dy)
  neighborhood_open : IsOpen neighborhood
  domain_subset : productDomain dx K ⊆ neighborhood
  gradient_correct : ∀ i z, z ∈ neighborhood →
    HasGradientAt (component i) (componentGradient i z) z
  average_dual_concave : ∀ x, ConcaveOn ℝ K.carrier
    (fun y => componentAverage component (jointPoint x y))
  initialPoint : PrimalSpace dx
  value_bddBelow : BddBelow (Set.range (primalObjective K component))
  initial_gap : primalObjective K component initialPoint -
    sInf (Set.range (primalObjective K component)) ≤ p.gap

namespace Problem

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

def individualSmooth (P : Problem p dx dy K) : Prop :=
  IndividualSmooth P.componentGradient (productDomain dx K) p.L

def averagedSmooth (P : Problem p dx dy K) : Prop :=
  AveragedSmooth P.componentGradient (productDomain dx K) p.L

theorem individual_implies_averaged (P : Problem p dx dy K)
    (h : P.individualSmooth) : P.averagedSmooth :=
  IndividualSmooth.averagedSmooth p.L_pos.le h

/-- Component gradients are genuine derivatives at every allowed query. -/
theorem hasGradientAt_on_domain (P : Problem p dx dy K)
    (i : Fin p.n) (z : JointSpace dx dy) (hz : z ∈ productDomain dx K) :
    HasGradientAt (P.component i) (P.componentGradient i z) z :=
  P.gradient_correct i z (P.domain_subset hz)

theorem average_dual_continuous (P : Problem p dx dy K) (x : PrimalSpace dx) :
    ContinuousOn (fun y => componentAverage P.component (jointPoint x y)) K.carrier := by
  have hpoint : Continuous (fun y : DualSpace dy => jointPoint x y) :=
    (WithLp.prod_continuous_toLp 2 _ _).comp (continuous_const.prodMk continuous_id)
  have hi (i : Fin p.n) : ContinuousOn (fun y => P.component i (jointPoint x y)) K.carrier := by
    intro y hy
    have hz : jointPoint x y ∈ productDomain dx K := hy
    exact ((P.hasGradientAt_on_domain i _ hz).continuousAt.comp hpoint.continuousAt).continuousWithinAt
  exact continuousOn_const.mul (continuousOn_finsetSum Finset.univ (fun i _ => hi i))

/-- Compactness makes `Phi` an actual maximum, not just a formal supremum. -/
theorem exists_dual_maximizer (P : Problem p dx dy K) (x : PrimalSpace dx) :
    ∃ y ∈ K.carrier, primalObjective K P.component x =
      componentAverage P.component (jointPoint x y) := by
  obtain ⟨y, hy, hmax⟩ := K.compact.exists_isMaxOn K.nonempty (P.average_dual_continuous x)
  refine ⟨y, hy, le_antisymm ?_ ?_⟩
  · apply csSup_le (K.nonempty.image _)
    rintro v ⟨y', hy', rfl⟩
    exact hmax hy'
  · apply le_csSup
    · refine ⟨componentAverage P.component (jointPoint x y), ?_⟩
      rintro v ⟨y', hy', rfl⟩
      exact hmax hy'
    · exact ⟨y, hy, rfl⟩

/-- AS controls the actual average of the component gradient vectors. -/
theorem average_gradient_lipschitz (P : Problem p dx dy K) (h : P.averagedSmooth) :
    ∀ z ∈ productDomain dx K, ∀ z' ∈ productDomain dx K,
      ‖averageMap P.componentGradient z - averageMap P.componentGradient z'‖ ≤
        p.L * ‖z - z'‖ :=
  AveragedSmooth.average_lipschitz p.n_pos p.L_pos.le h

/-- The averaged gradient map is the derivative of the actual finite average. -/
theorem hasGradientAt_average (P : Problem p dx dy K)
    (z : JointSpace dx dy) (hz : z ∈ productDomain dx K) :
    HasGradientAt (componentAverage P.component) (averageMap P.componentGradient z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (P.hasGradientAt_on_domain i z hz).hasFDerivAt)
  convert hsum.const_smul ((p.n : ℝ)⁻¹) using 1
  · rfl
  · simp [averageMap, map_smul, map_sum]

end Problem

/-- A complete component-oracle query, whose dual point is in the known domain. -/
abbrev OracleQuery {dy : ℕ} {D : ℝ} (n dx : ℕ) (K : KnownDualDomain dy D) :=
  Fin n × PrimalSpace dx × K.carrier

/-- The exact value and both partial gradients returned by the oracle. -/
abbrev OracleAnswer (dx dy : ℕ) := ℝ × PrimalSpace dx × DualSpace dy

def queryPoint {n dx dy : ℕ} {D : ℝ} {K : KnownDualDomain dy D}
    (q : OracleQuery n dx K) : JointSpace dx dy := jointPoint q.2.1 q.2.2.val

def oracleResponse {p : ProblemParameters} {dx dy : ℕ}
    {K : KnownDualDomain dy p.diameter} (P : Problem p dx dy K)
    (q : OracleQuery p.n dx K) : OracleAnswer dx dy :=
  (P.component q.1 (queryPoint q),
    (P.componentGradient q.1 (queryPoint q)).fst,
    (P.componentGradient q.1 (queryPoint q)).snd)

theorem queryPoint_mem_domain {n dx dy : ℕ} {D : ℝ} {K : KnownDualDomain dy D}
    (q : OracleQuery n dx K) : queryPoint q ∈ productDomain dx K := q.2.2.property

theorem oracleResponse_hasGradientAt {p : ProblemParameters} {dx dy : ℕ}
    {K : KnownDualDomain dy p.diameter} (P : Problem p dx dy K)
    (q : OracleQuery p.n dx K) :
    HasGradientAt (P.component q.1)
      (jointPoint (oracleResponse P q).2.1 (oracleResponse P q).2.2) (queryPoint q) := by
  change HasGradientAt (P.component q.1) (P.componentGradient q.1 (queryPoint q)) (queryPoint q)
  exact P.hasGradientAt_on_domain q.1 _ (queryPoint_mem_domain q)

namespace OraclePolicy

variable {n dx dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D)

abbrev Observation := OracleQuery n dx K × OracleAnswer dx dy
abbrev History := Σ t : ℕ, Fin t → Observation K (n := n) (dx := dx)
abbrev Action := PrimalSpace dx ⊕ OracleQuery n dx K

def emptyHistory : History K (n := n) (dx := dx) := ⟨0, Fin.elim0⟩

def appendHistory (h : History K (n := n) (dx := dx))
    (o : Observation K (n := n) (dx := dx)) : History K (n := n) (dx := dx) :=
  ⟨h.1 + 1, Fin.snoc h.2 o⟩

/-- An arbitrary adaptive policy with measurable dependence on its private seed
and the entire transcript. `final` also permits unqueried output points. -/
structure AdaptivePolicy (Ω : Type*) [MeasurableSpace Ω] where
  next : Ω → History K (n := n) (dx := dx) → Action K (n := n) (dx := dx)
  final : Ω → History K (n := n) (dx := dx) → PrimalSpace dx
  next_measurable : Measurable (Function.uncurry next)
  final_measurable : Measurable (Function.uncurry final)

def runAux {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω) :
    ℕ → History K (n := n) (dx := dx) → PrimalSpace dx × History K (n := n) (dx := dx)
  | 0, h => (P.final seed h, h)
  | t + 1, h => match P.next seed h with
    | Sum.inl x => (x, h)
    | Sum.inr q => runAux P oracle seed t (appendHistory K h (q, oracle q))

def run {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω) (budget : ℕ) :=
  runAux K P oracle seed budget (emptyHistory K)

/-- The query budget holds for every seed and every possible answer oracle. -/
theorem runAux_budget {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω) (t : ℕ)
    (h : History K (n := n) (dx := dx)) :
    (runAux K P oracle seed t h).2.1 ≤ h.1 + t := by
  induction t generalizing h with
  | zero => simp [runAux]
  | succ t ih =>
    cases hnext : P.next seed h with
    | inl x =>
      simpa [runAux, hnext] using Nat.le_add_right h.1 (t + 1)
    | inr q =>
      have hi := ih (appendHistory K h (q, oracle q))
      simpa [runAux, hnext, appendHistory, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

theorem run_budget {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω) (budget : ℕ) :
    (run K P oracle seed budget).2.1 ≤ budget := by
  simpa [run, emptyHistory] using runAux_budget K P oracle seed budget (emptyHistory K)

def Consistent (oracle : OracleQuery n dx K → OracleAnswer dx dy)
    (h : History K (n := n) (dx := dx)) : Prop :=
  ∀ j, (h.2 j).2 = oracle (h.2 j).1

theorem consistent_empty (oracle : OracleQuery n dx K → OracleAnswer dx dy) :
    Consistent K oracle (emptyHistory K) := fun j => Fin.elim0 j

theorem Consistent.append {oracle : OracleQuery n dx K → OracleAnswer dx dy}
    {h : History K (n := n) (dx := dx)} (hh : Consistent K oracle h)
    (q : OracleQuery n dx K) : Consistent K oracle (appendHistory K h (q, oracle q)) := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [appendHistory]
  · simpa [appendHistory] using hh i

theorem runAux_consistent {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω) (t : ℕ)
    (h : History K (n := n) (dx := dx)) (hh : Consistent K oracle h) :
    Consistent K oracle (runAux K P oracle seed t h).2 := by
  induction t generalizing h with
  | zero => exact hh
  | succ t ih =>
    simp only [runAux]
    split
    · exact hh
    · exact ih _ (hh.append K _)

theorem run_consistent {Ω : Type*} [MeasurableSpace Ω]
    (P : AdaptivePolicy K (n := n) (dx := dx) Ω)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω) (budget : ℕ) :
    Consistent K oracle (run K P oracle seed budget).2 :=
  runAux_consistent K P oracle seed budget _ (consistent_empty K oracle)

end OraclePolicy

/-- The literal infimum definition of the Moreau envelope at parameter `1/(2L)`. -/
def problemMoreauEnvelope {p : ProblemParameters} {dx dy : ℕ}
    {K : KnownDualDomain dy p.diameter} (P : Problem p dx dy K) (c : PrimalSpace dx) : ℝ :=
  sInf (Set.range (fun x => primalObjective K P.component x + p.L * ‖x - c‖ ^ 2))

/-- Requiring a real derivative prevents the total `gradient` function from
counting nondifferentiability as a zero gradient. -/
def StationaryOutput {p : ProblemParameters} {dx dy : ℕ}
    {K : KnownDualDomain dy p.diameter} (P : Problem p dx dy K) (x : PrimalSpace dx) : Prop :=
  ∃ g, HasGradientAt (problemMoreauEnvelope P) g x ∧ ‖g‖ ≤ p.epsilon

/-- Private randomness may have any probability space; it is not public oracle data. -/
structure RandomizedPolicy {n dx dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D) where
  Seed : Type
  seedSpace : MeasurableSpace Seed
  law : @Measure Seed seedSpace
  law_probability : @IsProbabilityMeasure Seed seedSpace law
  policy : @OraclePolicy.AdaptivePolicy n dx dy D K Seed seedSpace

def Success {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
    (A : RandomizedPolicy K (n := p.n) (dx := dx))
    (P : Problem p dx dy K) (budget : ℕ) : Prop :=
  letI : MeasurableSpace A.Seed := A.seedSpace
  let event := {seed | StationaryOutput P
    (OraclePolicy.run K A.policy (oracleResponse P) seed budget).1}
  @MeasurableSet A.Seed A.seedSpace event ∧ (2 / 3 : ℝ≥0∞) ≤ A.law event

inductive SmoothnessClass
  | individual
  | averaged

def Problem.inClass {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
    (P : Problem p dx dy K) : SmoothnessClass → Prop
  | .individual => P.individualSmooth
  | .averaged => P.averagedSmooth

/-- Uniform worst-case quantification: the policy knows dimensions and the dual
domain, and is chosen before the unknown component functions. -/
def ValidBudget (p : ProblemParameters) (mode : SmoothnessClass) (budget : ℕ) : Prop :=
  ∀ (dx dy : ℕ) (K : KnownDualDomain dy p.diameter) (x0 : PrimalSpace dx),
    ∃ A : RandomizedPolicy K (n := p.n) (dx := dx),
      ∀ P : Problem p dx dy K, P.initialPoint = x0 → P.inClass mode → Success A P budget

/-- IS is a subclass of AS, so an AS algorithm is valid for the IS class. -/
theorem validBudget_individual_of_averaged {p : ProblemParameters} {budget : ℕ}
    (h : ValidBudget p .averaged budget) : ValidBudget p .individual budget := by
  intro dx dy K x0
  obtain ⟨A, hA⟩ := h dx dy K x0
  refine ⟨A, fun P h0 hP => hA P h0 ?_⟩
  exact P.individual_implies_averaged hP

end

end NCConcave16991
