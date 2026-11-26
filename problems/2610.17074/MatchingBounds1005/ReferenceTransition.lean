import MatchingBounds1005.CensoredGaussianProcess

/-!
# The reference update as an accessible deterministic calculation

Only the old rows, their raw answers, the new rows, the visible signal, and
a private Gaussian vector enter an innovation response. The full rotation
and the hidden signal are absent from this interface.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.ReferenceTransition
open GaussianVector GaussianFitter AdaptiveGaussian PosteriorGaussian SequentialPosterior

abbrev State (d T : ℕ) := (Fin T → Vec d) × (Fin T → ℝ)
abbrev Input (d T : ℕ) := State d T × ((Fin T → Vec d) × Vec d)

def transition {d T : ℕ} (σ : ℝ) (p : Input d T × Vec d) : Fin T → ℝ :=
  rowResponse p.1.2.1
    (fitter p.1.1.1 p.1.1.2 + projection (Submodule.span ℝ (Set.range p.1.1.1))ᗮ (p.1.2.2 + σ • p.2))

attribute [local irreducible] projection fitter rowResponse Submodule.span Submodule.orthogonal

theorem transition_measurable {d T : ℕ} (σ : ℝ) : Measurable (transition (d := d) (T := T) σ) := by
  let oldRows := fun h : Input d T => h.1.1
  let oldY := fun h : Input d T => h.1.2
  let newRows := fun h : Input d T => h.2.1
  let visible := fun h : Input d T => h.2.2
  have ho : ∀ i, Measurable (fun h => oldRows h i) :=
    fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
  have hy : ∀ i, Measurable (fun h => oldY h i) :=
    fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hn : ∀ i, Measurable (fun h => newRows h i) :=
    fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hv : Measurable visible := measurable_snd.comp measurable_snd
  have hfit := measurable_fitter oldRows oldY ho hy
  have hin : Measurable (fun p : Input d T × Vec d => (p.1, visible p.1 + σ • p.2)) :=
    measurable_fst.prodMk ((hv.comp measurable_fst).add (measurable_const.smul measurable_snd))
  have hQ := (measurable_complement (fun h => Submodule.span ℝ (Set.range (oldRows h)))
    (measurable_spanProjection oldRows ho)).comp hin
  have hp := (measurable_fst : Measurable (Prod.fst : Input d T × Vec d → Input d T)).prodMk
    ((hfit.comp measurable_fst).add hQ)
  exact (measurable_rowResponse_family newRows hn).comp hp

/-- The deterministic implementation fits every newly emitted response. -/
theorem transition_consistent {d T : ℕ} (σ : ℝ) (p : Input d T × Vec d) :
    rowResponse p.1.2.1 (fitter p.1.2.1 (transition σ p)) = transition σ p :=
  fitter_exact p.1.2.1 _

/-- History representation is irrelevant: equal accessible inputs and equal
private noise produce identical raw responses. -/
theorem transition_congr {d T : ℕ} (σ : ℝ) (a b : Input d T) (hab : a = b) (z : Vec d) :
    transition σ (a, z) = transition σ (b, z) := congrArg (fun x => transition σ (x, z)) hab

end MatchingBounds1005.ReferenceTransition
