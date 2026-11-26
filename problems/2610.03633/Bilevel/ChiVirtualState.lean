import Bilevel.ChiVirtualFormulaContinuity
import Bilevel.PrefixGramMeasurable

/-! Concrete virtual state data: one discrete progress counter and disclosed
column arrays. Prefix lengths are deterministic functions of that counter. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

abbrev VirtualState (M : Node E) (D : Geometry F) := ℕ × HierarchyData M D

def ValidState (M : Node E) (D : Geometry F) (rM : ℕ → ℕ)
    (r : ℕ → ℕ → List ℕ → ℕ) (p : VirtualState M D) : Prop :=
  PrefixGram M.n (rM p.1) p.2.1 ∧ ∀ j I,PrefixGram (D j I).n (r p.1 j I) (p.2.2 j I)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

theorem validState_measurable (M : Node E) (D : Geometry F) (rM : ℕ → ℕ)
    (r : ℕ → ℕ → List ℕ → ℕ) : MeasurableSet {p : VirtualState M D | ValidState M D rM r p} := by
  have hm : MeasurableSet {p : VirtualState M D | PrefixGram M.n (rM p.1) p.2.1} :=
    prefixGram_of_measurable M.n (fun p : VirtualState M D => rM p.1) ((measurable_of_countable rM).comp measurable_fst)
      (fun p : VirtualState M D => p.2.1) measurable_snd.fst
  have hn (j : ℕ) (I : List ℕ) : MeasurableSet {p : VirtualState M D |
      PrefixGram (D j I).n (r p.1 j I) (p.2.2 j I)} :=
    prefixGram_of_measurable (D j I).n (fun p : VirtualState M D => r p.1 j I)
      ((measurable_of_countable (fun q => r q j I)).comp measurable_fst)
      (fun p : VirtualState M D => p.2.2 j I)
      ((measurable_pi_apply I).comp ((measurable_pi_apply j).comp measurable_snd.snd))
  exact hm.inter (by simpa only [Set.iInter_setOf] using
    MeasurableSet.iInter (fun j => MeasurableSet.iInter (hn j)))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem virtualActive_state_continuous (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (c θ : ℝ) (s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ) :
    Continuous (fun p : VirtualState M D × Full (Joint E (Blocks m F)) s =>
      virtualActive m M D J (rM p.1.1) (r p.1.1) p.1.2.1 p.1.2.2 c θ s index radialIndex fineIndex rad R dn p.2) := by
  have h : Continuous (fun p : ℕ × (HierarchyData M D × Full (Joint E (Blocks m F)) s) =>
      virtualActive m M D J (rM p.1) (r p.1) p.2.1.1 p.2.1.2 c θ s index radialIndex fineIndex rad R dn p.2.2) :=
    continuous_prod_of_discrete_left.mpr (fun q =>
      virtualActive_continuous m M D J (rM q) (r q) c θ s index radialIndex fineIndex rad R dn)
  exact Continuous.comp
    (f := fun p : VirtualState M D × Full (Joint E (Blocks m F)) s => (p.1.1,(p.1.2,p.2)))
    (g := fun p : ℕ × (HierarchyData M D × Full (Joint E (Blocks m F)) s) =>
      virtualActive m M D J (rM p.1) (r p.1) p.2.1.1 p.2.1.2 c θ s index radialIndex fineIndex rad R dn p.2.2)
    h (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem virtualInactive_state_continuous (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (rM : ℕ → ℕ) (r : ℕ → ℕ → List ℕ → ℕ) (c θ : ℝ) (s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ) :
    Continuous (fun p : VirtualState M D × Full (Joint E (Blocks m F)) s =>
      virtualInactive m M D J (rM p.1.1) (r p.1.1) p.1.2.1 p.1.2.2 c θ s index radialIndex fineIndex rad R dn p.2) := by
  have h : Continuous (fun p : ℕ × (HierarchyData M D × Full (Joint E (Blocks m F)) s) =>
      virtualInactive m M D J (rM p.1) (r p.1) p.2.1.1 p.2.1.2 c θ s index radialIndex fineIndex rad R dn p.2.2) :=
    continuous_prod_of_discrete_left.mpr (fun q =>
      virtualInactive_continuous m M D J (rM q) (r q) c θ s index radialIndex fineIndex rad R dn)
  exact Continuous.comp
    (f := fun p : VirtualState M D × Full (Joint E (Blocks m F)) s => (p.1.1,(p.1.2,p.2)))
    (g := fun p : ℕ × (HierarchyData M D × Full (Joint E (Blocks m F)) s) =>
      virtualInactive m M D J (rM p.1) (r p.1) p.2.1.1 p.2.1.2 c θ s index radialIndex fineIndex rad R dn p.2.2)
    h (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))

end Bilevel.ChiPrefixEvaluation
