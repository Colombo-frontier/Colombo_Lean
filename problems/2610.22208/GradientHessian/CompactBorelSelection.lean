import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic

/-! A Borel selector for a closed relation with nonempty compact metric
fibers. The selector is constructed from least dense-ball choices and
Cantor intersections, so no measurable-choice principle is assumed. -/

noncomputable section
namespace GradientHessian.CompactBorelSelection
open Classical Set Metric Filter Topology MeasureTheory

local instance : MeasurableSpace (List ℕ) := ⊤
local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

variable {P X : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

def cell : List ℕ → Set X
  | [] => univ
  | j::w => cell w ∩ closedBall (TopologicalSpace.denseSeq X j) (1/((w.length:ℝ)+1))

theorem cell_closed (w : List ℕ) : IsClosed (cell (X := X) w) := by
  induction w with
  | nil => exact isClosed_univ
  | cons j w ih => exact ih.inter isClosed_closedBall

def feasible (R : Set (P × X)) (p : P) (w : List ℕ) : Prop :=
  ∃ x ∈ cell (X := X) w, (p,x) ∈ R

theorem feasible_closed {R : Set (P × X)} (hR : IsClosed R) (w : List ℕ) :
    IsClosed {p | feasible R p w} := by
  have hh := isClosedMap_fst_of_compactSpace (X := P) (Y := X)
    (R ∩ Prod.snd ⁻¹' cell w) (hR.inter ((cell_closed w).preimage continuous_snd))
  convert hh using 1
  ext p
  simp only [feasible,mem_setOf_eq,mem_image,mem_inter_iff,mem_preimage,Prod.exists]
  constructor
  · rintro ⟨x,hx,hr⟩
    exact ⟨p,x,⟨hr,hx⟩,rfl⟩
  · rintro ⟨p',x,⟨hr,hx⟩,rfl⟩
    exact ⟨x,hx,hr⟩

theorem next_exists (R : Set (P × X)) (p : P) (w : List ℕ) :
    ∃ j, ¬feasible R p w ∨ feasible R p (j::w) := by
  by_cases hf : feasible R p w
  · obtain ⟨x,hx,hr⟩ := hf
    obtain ⟨j,hj⟩ := (TopologicalSpace.denseRange_denseSeq X).exists_dist_lt x
      (by positivity : 0<(1:ℝ)/((w.length:ℝ)+1))
    exact ⟨j,Or.inr ⟨x,⟨hx,hj.le⟩,hr⟩⟩
  · exact ⟨0,Or.inl hf⟩

def next (R : Set (P × X)) (p : P) (w : List ℕ) : ℕ :=
  Nat.find (next_exists R p w)

theorem next_spec (R : Set (P × X)) (p : P) (w : List ℕ) (hf : feasible R p w) :
    feasible R p (next R p w::w) := by
  exact (Nat.find_spec (next_exists R p w)).resolve_left (not_not.mpr hf)

theorem next_measurable {R : Set (P × X)} (hR : IsClosed R) :
    Measurable (fun q : P × List ℕ => next R q.1 q.2) := by
  apply measurable_from_prod_countable
  intro w
  exact measurable_find (fun p => next_exists R p w) (fun j =>
    (feasible_closed hR w).measurableSet.compl.union (feasible_closed hR (j::w)).measurableSet)

def history (R : Set (P × X)) (p : P) : ℕ → List ℕ
  | 0 => []
  | n+1 => next R p (history R p n)::history R p n

theorem history_length (R : Set (P × X)) (p : P) (n : ℕ) :
    (history R p n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [history,List.length_cons,ih]

theorem history_measurable {R : Set (P × X)} (hR : IsClosed R) (n : ℕ) :
    Measurable (fun p => history R p n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hn := (next_measurable hR).comp (measurable_id.prodMk ih)
    exact (measurable_of_countable (fun q : ℕ × List ℕ => q.1::q.2)).comp (hn.prodMk ih)

theorem history_feasible (R : Set (P × X)) (hne : ∀ p, ∃ x, (p,x) ∈ R) (p : P) (n : ℕ) :
    feasible R p (history R p n) := by
  induction n with
  | zero => obtain ⟨x,hx⟩ := hne p; exact ⟨x,mem_univ _,hx⟩
  | succ n ih => exact next_spec R p (history R p n) ih

def fiber (R : Set (P × X)) (p : P) (n : ℕ) : Set X :=
  cell (history R p n) ∩ {x | (p,x) ∈ R}

theorem fiber_closed {R : Set (P × X)} (hR : IsClosed R) (p : P) (n : ℕ) :
    IsClosed (fiber R p n) :=
  (cell_closed _).inter (hR.preimage (continuous_const.prodMk continuous_id))

theorem intersection_nonempty {R : Set (P × X)} (hR : IsClosed R)
    (hne : ∀ p, ∃ x, (p,x) ∈ R) (p : P) : (⋂ n, fiber R p n).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · intro n x hx
    exact ⟨hx.1.1,hx.2⟩
  · intro n
    obtain ⟨x,hx,hr⟩ := history_feasible R hne p n
    exact ⟨x,hx,hr⟩
  · exact (fiber_closed hR p 0).isCompact
  · exact fiber_closed hR p

def selector {R : Set (P × X)} (hR : IsClosed R) (hne : ∀ p, ∃ x, (p,x) ∈ R) (p : P) : X :=
  (intersection_nonempty hR hne p).choose

theorem selector_mem {R : Set (P × X)} (hR : IsClosed R) (hne : ∀ p, ∃ x, (p,x) ∈ R) (p : P) :
    (p,selector hR hne p) ∈ R :=
  (mem_iInter.mp (intersection_nonempty hR hne p).choose_spec 0).2

theorem selector_dist {R : Set (P × X)} (hR : IsClosed R) (hne : ∀ p, ∃ x, (p,x) ∈ R)
    (p : P) (n : ℕ) :
    dist (TopologicalSpace.denseSeq X (next R p (history R p n))) (selector hR hne p) ≤1/((n:ℝ)+1) := by
  have hh := (mem_iInter.mp (intersection_nonempty hR hne p).choose_spec (n+1)).1.2
  rw [dist_comm]
  simpa only [history_length,mem_closedBall,selector] using hh

theorem selector_measurable {R : Set (P × X)} (hR : IsClosed R)
    (hne : ∀ p, ∃ x, (p,x) ∈ R) : Measurable (selector hR hne) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n p => TopologicalSpace.denseSeq X (next R p (history R p n)))
  · intro n
    exact (measurable_of_countable (TopologicalSpace.denseSeq X)).comp
      ((next_measurable hR).comp (measurable_id.prodMk (history_measurable hR n)))
  · apply tendsto_pi_nhds.mpr
    intro p
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (selector_dist hR hne p)
      tendsto_one_div_add_atTop_nhds_zero_nat

theorem exists_measurable_selector {R : Set (P × X)} (hR : IsClosed R)
    (hne : ∀ p, ∃ x, (p,x) ∈ R) : ∃ f : P → X, Measurable f ∧ ∀ p, (p,f p) ∈ R :=
  ⟨selector hR hne,selector_measurable hR hne,selector_mem hR hne⟩

def minimumRelation (f : P → X → ℝ) : Set (P × X) :=
  {q | ∀ y, f q.1 q.2 ≤ f q.1 y}

theorem minimumRelation_closed {f : P → X → ℝ}
    (hf : Continuous (fun q : P × X => f q.1 q.2)) : IsClosed (minimumRelation f) := by
  have he : minimumRelation f = ⋂ y : X, {q : P × X | f q.1 q.2 ≤ f q.1 y} := by
    ext q
    simp only [minimumRelation,mem_setOf_eq,mem_iInter]
  rw [he]
  exact isClosed_iInter (fun y => isClosed_le hf (hf.comp (continuous_fst.prodMk continuous_const)))

theorem minimumRelation_nonempty {f : P → X → ℝ}
    (hf : Continuous (fun q : P × X => f q.1 q.2)) (p : P) :
    ∃ x, (p,x) ∈ minimumRelation f := by
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set X).Nonempty)
    (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
  exact ⟨x,fun y => hx (mem_univ y)⟩

def minimizer {f : P → X → ℝ} (hf : Continuous (fun q : P × X => f q.1 q.2)) : P → X :=
  selector (minimumRelation_closed hf) (minimumRelation_nonempty hf)

theorem minimizer_measurable {f : P → X → ℝ}
    (hf : Continuous (fun q : P × X => f q.1 q.2)) : Measurable (minimizer hf) :=
  selector_measurable (minimumRelation_closed hf) (minimumRelation_nonempty hf)

theorem minimizer_spec {f : P → X → ℝ}
    (hf : Continuous (fun q : P × X => f q.1 q.2)) (p : P) (y : X) :
    f p (minimizer hf p) ≤ f p y :=
  selector_mem (minimumRelation_closed hf) (minimumRelation_nonempty hf) p y

end GradientHessian.CompactBorelSelection
