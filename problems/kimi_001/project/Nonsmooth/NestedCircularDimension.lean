import Nonsmooth.ActualNestedCircularPolicy

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem circularGeometryState_dimension (R ε : ℝ) (N : ℕ) (h : List ℤ) :
    Module.finrank ℝ (circularGeometryState (E := E) R ε N h).2 =
      max 1 (Module.finrank ℝ E - h.length) := by
  have hdim : 0 < Module.finrank ℝ E := Module.finrank_pos
  induction h with
  | nil =>
    change Module.finrank ℝ (⊤ : Submodule ℝ E) = max 1 (Module.finrank ℝ E - 0)
    rw [finrank_top, Nat.sub_zero, max_eq_right (show 1 ≤ Module.finrank ℝ E by omega)]
  | cons j h ih =>
    let K := (circularGeometryState (E := E) R ε N h).2
    change Module.finrank ℝ K = max 1 (Module.finrank ℝ E - h.length) at ih
    change Module.finrank ℝ (subspaceCircularSection K N j) =
      max 1 (Module.finrank ℝ E - (h.length + 1))
    by_cases hd : 2 ≤ Module.finrank ℝ K
    · have hdrop := subspaceCircularSection_dimension K N j hd
      omega
    · rw [subspaceCircularSection_terminal K N j (lt_of_not_ge hd)]
      omega

theorem circularGeometryState_line (R ε : ℝ) (N : ℕ) (h : List ℤ)
    (hlen : Module.finrank ℝ E - 1 ≤ h.length) :
    Module.finrank ℝ (circularGeometryState (E := E) R ε N h).2 = 1 := by
  rw [circularGeometryState_dimension]
  omega

theorem nestedCircularController_final_line (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) :
    Module.finrank ℝ (circularGeometryState (E := E) R ε N
      (nestedCircularController R ε N hR hε hε1 f (Module.finrank ℝ E - 1)).entries).2 = 1 := by
  apply circularGeometryState_line
  rw [nestedCircularController_length]

theorem nestedCircularPolicy_norm_le_half (R ε : ℝ) (N : ℕ) (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (f : E → ℝ) (m : ℕ) :
    ‖((nestedCircularPolicy R ε N hR hε hε1).result
      (fun x => f x.val) () (m * (3 * N + 4))).val‖ ≤ R / 2 := by
  rw [nestedCircularPolicy_result_exact]
  exact circularGeometryState_norm_le_half hR hε hε1 N _

end
end Nonsmooth
