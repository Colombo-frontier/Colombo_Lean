import MatchingBounds1005.AccessibleReferenceCompiler
import MatchingBounds1005.ReferenceTransition

/-!
# Concrete private-noise Gaussian query commands

The query command computes the reference tensor response from its accessible
input and a stored private Gaussian vector. The physical quadratic oracle
response is supplied separately; a measurable continuation assembles the
first-order oracle and updates the algorithm. The command never inspects U.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.GaussianReferenceCommand
open GaussianVector AccessibleReferenceCompiler ScheduledHaar ReferenceTransition

universe u
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {S : Type u} [MeasurableSpace S] {d T : ℕ}

def gaussianUpdate (σ : ℝ) (input : S → Input d T) (noise : S → Vec d)
    (finish : S × (E × (Fin T → ℝ)) → S) (p : S × E) : S :=
  finish (p.1, (p.2, transition σ (input p.1, noise p.1)))

theorem gaussianUpdate_measurable (σ : ℝ) (input : S → Input d T) (noise : S → Vec d)
    (finish : S × (E × (Fin T → ℝ)) → S) (hi : Measurable input) (hn : Measurable noise)
    (hf : Measurable finish) : Measurable (gaussianUpdate σ input noise finish) := by
  have ht : Measurable (fun s : S => transition σ (input s, noise s)) :=
    (transition_measurable σ).comp (hi.prodMk hn)
  exact hf.comp (measurable_fst.prodMk (measurable_snd.prodMk (ht.comp measurable_fst)))

def queryCommand (σ : ℝ) (point : S → E) (hp : Measurable point)
    (input : S → Input d T) (hi : Measurable input) (noise : S → Vec d) (hn : Measurable noise)
    (finish : S × (E × (Fin T → ℝ)) → S) (hf : Measurable finish) :
    PhysicalRequest (E := E) S × Update (E := E) S :=
  (⟨point, hp⟩, ⟨gaussianUpdate σ input noise finish, gaussianUpdate_measurable σ input noise finish hi hn hf⟩)

/-- One source command performs exactly one quadratic query and one
simultaneous Gaussian tensor response, then applies the stated continuation. -/
theorem queryCommand_run (σ : ℝ) (point : S → E) (hp : Measurable point)
    (input : S → Input d T) (hi : Measurable input) (noise : S → Vec d) (hn : Measurable noise)
    (finish : S × (E × (Fin T → ℝ)) → S) (hf : Measurable finish)
    (Q U : E →L[ℝ] E) (s : S) :
    AccessibleReferenceCompiler.run [.query]
      (queryCommand σ point hp input hi noise hn finish hf, PUnit.unit) Q U s =
        finish (s, (U (Q (U.adjoint (point s))), transition σ (input s, noise s))) := rfl

/-- The actual SourcePolicy compilation has this same physical semantics.
The inverse answer included in the analyst's richer history is not used. -/
theorem compiled_queryCommand_run (σ : ℝ) (point : S → E) (hp : Measurable point)
    (input : S → Input d T) (hi : Measurable input) (noise : S → Vec d) (hn : Measurable noise)
    (finish : S × (E × (Fin T → ℝ)) → S) (hf : Measurable finish)
    (Q U : E →L[ℝ] E) (s : S) :
    let M : Machine (E := E) (S := S) [.query] :=
      (queryCommand σ point hp input hi noise hn finish hf, PUnit.unit)
    AccessibleReferenceCompiler.decode [.query] M id
      ((AccessibleReferenceCompiler.compile [.query] M id measurable_id).run [.query] Q U s) =
        finish (s, (U (Q (U.adjoint (point s))), transition σ (input s, noise s))) := by
  dsimp only
  rw [AccessibleReferenceCompiler.compile_correct]
  rfl

end MatchingBounds1005.GaussianReferenceCommand
