import SecondOrder.EpochPath

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

/-- The address of a physical move lies inside its actual truncated epoch.
The inverse is the epoch boundary plus the local offset. -/
theorem epochAddress_physical {N q t : ℕ} (hq : 0 < q) (g : ℕ → Bool) (ht : t < N) :
    let a := epochAddress q g t
    a.2 < epochLength N q g a.1 ∧ epochBoundary N q g a.1+a.2=t := by
  have hi := (epoch_interval_iff N q g (epochOfStep q g t) t).mpr ⟨ht,rfl⟩
  have hs := epochBoundary_eq_clock hq ht (show epochOfStep q g t=epochOfStep q g t from rfl)
  have he := epochLength_add_start N q g (epochOfStep q g t)
  dsimp only [epochAddress]
  rw [← hs]
  omega

/-- Reindex actual physical moves by their epoch and local position.
Every move occurs once; unvisited epochs contribute an empty sum. -/
theorem sum_epoch_local {V : Type*} [AddCommMonoid V] {N M q : ℕ}
    (hNM : N ≤ M) (hq : 0 < q) (g : ℕ → Bool) (f : ℕ → ℕ → V) :
    (∑ t ∈ Finset.range N, f (epochAddress q g t).1 (epochAddress q g t).2) =
      ∑ e : Fin M, ∑ k ∈ Finset.range (epochLength N q g e.val), f e.val k := by
  rw [Fin.sum_univ_eq_sum_range (fun e => ∑ k ∈ Finset.range (epochLength N q g e), f e k) M,
    Finset.sum_sigma']
  apply Finset.sum_bij (fun t _ => Sigma.mk (epochAddress q g t).1 (epochAddress q g t).2)
  · intro t ht
    have ht' := Finset.mem_range.mp ht
    have hh := epochAddress_physical hq g ht'
    apply Finset.mem_sigma.mpr
    exact ⟨Finset.mem_range.mpr ((epochOfStep_le q g t).trans_lt (ht'.trans_le hNM)),
      Finset.mem_range.mpr hh.1⟩
  · intro t ht u hu he
    have ht' := (epochAddress_physical hq g (Finset.mem_range.mp ht)).2
    have hu' := (epochAddress_physical hq g (Finset.mem_range.mp hu)).2
    have he1 := congrArg Sigma.fst he
    have he2 := congrArg (fun a : Sigma (fun _ : ℕ => ℕ) => a.2) he
    have ha : epochAddress q g t=epochAddress q g u := Prod.ext he1 he2
    rw [ha] at ht'
    exact ht'.symm.trans hu'
  · intro a ha
    obtain ⟨he,hk⟩ := Finset.mem_sigma.mp ha
    have hk' := Finset.mem_range.mp hk
    have ht := epoch_local_time hk'
    refine ⟨epochBoundary N q g a.1+a.2,Finset.mem_range.mpr ht.1,?_⟩
    have hh := epoch_local_address hq hk'
    cases a
    simp only [hh]
  · intro t ht
    rfl

end
end SecondOrder
