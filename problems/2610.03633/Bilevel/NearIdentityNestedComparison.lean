import Bilevel.NearIdentitySignalComparison

/-! Actual inverses on nested restricted spaces. This generic comparison
keeps its inactive invariance premise explicit; concrete hierarchy support
discharges it in the construction-specific application. -/
noncomputable section
namespace Bilevel.NearIdentityInverse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def subspaceInclusion (W V : Submodule ℝ E) (hWV : W≤V) (u : W) : V := ⟨u,hWV u.property⟩

theorem nested_inverse_compare (W V : Submodule ℝ E) [CompleteSpace W] [CompleteSpace V]
    (hWV : W≤V) {δa δi : NNReal} (hδa : δa<1) (hδi : δi<1) {G H : E → E}
    (hG : LipschitzWith δa G) (hH : LipschitzWith δi H) (u : W) (t : Time)
    (hmem : H (restrictedInverse W hδi hH u t)∈W) (B : ℝ)
    (hb : ∀ z,‖G z-H z‖≤B) :
    ‖(restrictedInverse V hδa hG (subspaceInclusion W V hWV u) t:E)-
      (restrictedInverse W hδi hH u t:E)‖≤B/(1-(δa:ℝ)) := by
  let p := restrictedInverse W hδi hH u t
  have heq : (p:E)+(t:ℝ) • H p=(u:E) := restricted_ambient_equation W hδi hH u t hmem
  exact restricted_compare_point V hδa hG (subspaceInclusion W V hWV u)
    (subspaceInclusion W V hWV p) t B heq (hb p)

end Bilevel.NearIdentityInverse
