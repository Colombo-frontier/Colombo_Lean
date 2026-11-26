import RandomizedFO2003.MarkedPrefixGate

namespace RandomizedFO2003.Rotations

open SpectralCoordinates Primitives

universe u

variable {J : ℕ} (K : Fin J → ℕ) (r : Fin J → ℝ) (m t : ℕ)
  {H : Type u} [MeasurableSpace H] (plan : MarkedProgram (BlockSpace K) t H)
  (mark : H → BlockSpace K) (B α : ℝ)

/-- A non-flat query on the simultaneous good event must have exhausted
the spectral degree budget at that query, irrespective of later queries. -/
theorem MarkedProgram.prefixFlatEvent_exit_depth
    {p : ActionHistory (BlockSpace K) (markedActionCount t) H}
    (hp : p ∈ plan.prefixFlatEvent K r m t mark B α) (i : Fin t)
    (hexit : 1 / 4 < |radialReadout
      (direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r)
      B α (markedQueryTrace (BlockSpace K) t p i)|) :
    m < markedQueryDepth t (plan.authorizationTrace t p) 0 i := by
  by_contra hn
  exact (not_le_of_gt hexit) (hp i (Nat.le_of_not_gt hn))

/-- Any exit has an authorized predecessor, including a possible
authorization at that same query. This conclusion is pathwise. -/
theorem MarkedProgram.prefixFlatEvent_exit_authorized
    {p : ActionHistory (BlockSpace K) (markedActionCount t) H}
    (hp : p ∈ plan.prefixFlatEvent K r m t mark B α) (i : Fin t)
    (hexit : 1 / 4 < |radialReadout
      (direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r)
      B α (markedQueryTrace (BlockSpace K) t p i)|) :
    ∃ τ : Fin t, τ.val ≤ i.val ∧ plan.authorizationTrace t p τ = true := by
  have hd := plan.prefixFlatEvent_exit_depth K r m t mark B α hp i hexit
  by_contra hn
  push_neg at hn
  have hz := markedQueryDepth_before_authorization t (plan.authorizationTrace t p) i
    (fun j hj => Bool.eq_false_iff.mpr (hn j hj))
  omega

/-- If τ is the first authorization, any later non-flat query has index
at least τ+m. No conditioning on a random τ and no optional-stopping theorem
is needed: this holds for every eligible pair in the same realized event. -/
theorem MarkedProgram.prefixFlatEvent_exit_delay
    {p : ActionHistory (BlockSpace K) (markedActionCount t) H}
    (hp : p ∈ plan.prefixFlatEvent K r m t mark B α) (τ i : Fin t)
    (hfirst : plan.authorizationTrace t p τ = true)
    (hearlier : ∀ j : Fin t, j.val < τ.val → plan.authorizationTrace t p j = false)
    (hexit : 1 / 4 < |radialReadout
      (direction K (mark (ActionHistory.seed (BlockSpace K) (markedActionCount t) p)) r)
      B α (markedQueryTrace (BlockSpace K) t p i)|) : τ.val + m ≤ i.val := by
  have hd := plan.prefixFlatEvent_exit_depth K r m t mark B α hp i hexit
  have hτi : τ.val ≤ i.val := by
    by_contra hn
    have hz := markedQueryDepth_before_authorization t (plan.authorizationTrace t p) i
      (fun j hj => hearlier j (by omega))
    omega
  rw [markedQueryDepth_first_authorization t (plan.authorizationTrace t p) τ i hfirst hearlier hτi] at hd
  omega

end RandomizedFO2003.Rotations
