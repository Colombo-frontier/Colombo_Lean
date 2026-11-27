import Mathlib

/-!
The exact deterministic rank/reply ledger from Section 5.3. A finite transcript
has a set s of informative paid replies and a handle label for every reply.
At most two replies share a handle. This does not prove the stochastic
posterior or that every measurable oracle algorithm has a formal execution.
-/

namespace Task006HandleLedger

/-- The two-reply contract bounds the number of informative replies. -/
theorem replies_le_twice_handles
    {Q H : Type*} [DecidableEq Q] [DecidableEq H]
    (s : Finset Q) (handle : Q → H)
    (cap : ∀ h, (s.filter (fun q => handle q = h)).card ≤ 2) :
    s.card ≤ 2 * (s.image handle).card := by
  by_contra hnot
  have hlt : (s.image handle).card * 2 < s.card := by omega
  obtain ⟨h, _, hbad⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩) hlt
  exact (Nat.not_lt_of_ge (cap h)) hbad

/-- Each paid value supplies at most one linear-measurement vector. -/
theorem measurement_rank_le_twice_handles
    {Q H E : Type*} [DecidableEq Q] [DecidableEq H]
    [DecidableEq E] [AddCommGroup E] [Module ℝ E]
    (s : Finset Q) (handle : Q → H) (v : Q → E)
    (cap : ∀ h, (s.filter (fun q => handle q = h)).card ≤ 2) :
    Module.finrank ℝ (Submodule.span ℝ ((s.image v) : Set E)) ≤
      2 * (s.image handle).card := by
  classical
  calc
    Module.finrank ℝ (Submodule.span ℝ ((s.image v) : Set E))
        ≤ (s.image v).card := finrank_span_finset_le_card (R := ℝ) (s.image v)
    _ ≤ s.card := Finset.card_image_le
    _ ≤ 2 * (s.image handle).card := replies_le_twice_handles s handle cap

end Task006HandleLedger
