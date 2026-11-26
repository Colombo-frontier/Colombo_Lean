import NCConcave16991.DenseWeakFreshCompilerRun

/-! # A public learned-row cache discharges the compiler freshness invariant -/

noncomputable section

namespace NCConcave16991.DenseWeakHiding.FreshCompiler

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {S : Type*} {n D : ℕ}
  (request : S → Option (Fin n)) (advance : S → Reply D → S)
  (learned : S → Finset (Fin n))
  (hstep : ∀ s a, learned (advance s a) = (request s).elim (learned s) (fun i ↦ insert i (learned s)))

include hstep in
theorem seek_learned (fuel : ℕ) (s : S) :
    learned (seek request advance fuel s).2 = learned s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases h : request s with
      | some i => simp [seek,h]
      | none =>
          simp only [seek,h]
          rw [ih,hstep,h]
          rfl

theorem freshRequest_some_data (c : Context S n) (i : Fin n)
    (hi : freshRequest request advance c = some i) :
    0 < (seek request advance c.fuel c.state).1 ∧
      request (seek request advance c.fuel c.state).2 = some i ∧ i ∉ c.seen := by
  by_cases hz : (seek request advance c.fuel c.state).1 = 0
  · simp [freshRequest,hz] at hi
  · cases hr : request (seek request advance c.fuel c.state).2 with
    | none => simp [freshRequest,hr] at hi
    | some j =>
        by_cases hj : j ∈ c.seen
        · simp [freshRequest,hr,hj] at hi
        · have he : j = i := by simpa [freshRequest,hz,hr,hj] using hi
          subst i
          exact ⟨Nat.pos_of_ne_zero hz,rfl,hj⟩

def CacheInvariant (c : Context S n) : Prop := 0 < c.fuel → c.seen = learned c.state

include hstep in
theorem consume_cacheInvariant (hn : 0 < n) (c : Context S n) (a : Reply D)
    (hc : CacheInvariant learned c) : CacheInvariant learned (consume request advance hn c a) := by
  intro hp
  cases h : freshRequest request advance c with
  | none => simp [consume,h] at hp
  | some i =>
      have hd := freshRequest_some_data request advance c i h
      have hcf : 0 < c.fuel := hd.1.trans_le (seek_fuel_le request advance c.fuel c.state)
      have hk : c.seen = learned (seek request advance c.fuel c.state).2 :=
        (hc hcf).trans (seek_learned request advance learned hstep c.fuel c.state).symm
      simp only [consume,h,Option.isSome_some,ite_true]
      rw [hstep,hd.2.1]
      simp only [Option.elim_some]
      simpa only [pick,h,Option.getD_some] using congrArg (insert i) hk

include hstep in
theorem execute_cacheInvariant (hn : 0 < n) (table : Fin n → Reply D)
    (t : ℕ) (c : Context S n) (hc : CacheInvariant learned c) :
    CacheInvariant learned (execute request advance hn table t c) := by
  induction t generalizing c with
  | zero => exact hc
  | succ t ih => exact ih _ (consume_cacheInvariant request advance learned hstep hn c _ hc)

include hstep in
/-- The actual compiler freshness premise follows solely from the public
cache update and the client's local request freshness property. -/
theorem freshAlong_of_learned (hn : 0 < n) (table : Fin n → Reply D)
    (fuel : ℕ) (s : S) (hs : learned s = ∅)
    (hfresh : ∀ s i, request s = some i → i ∉ learned s) (r : ℕ) :
    FreshAlong request advance hn table (initial fuel s) r := by
  intro t ht i hp hr
  let c := execute request advance hn table t (initial fuel s)
  have hc : CacheInvariant learned c := execute_cacheInvariant request advance learned hstep hn table t
    (initial fuel s) (fun _ ↦ hs.symm)
  have hcf : 0 < c.fuel := hp.trans_le (seek_fuel_le request advance c.fuel c.state)
  have hk : c.seen = learned (seek request advance c.fuel c.state).2 :=
    (hc hcf).trans (seek_learned request advance learned hstep c.fuel c.state).symm
  rw [hk]
  exact hfresh _ i hr

end NCConcave16991.DenseWeakHiding.FreshCompiler
