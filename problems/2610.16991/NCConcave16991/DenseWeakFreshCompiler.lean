import NCConcave16991.DenseWeakAdaptivePath
import NCConcave16991.DenseWeakAdaptivePrefix

/-! # A bounded public optional-row machine compiled to fresh adaptive rows

None transitions use the public zero answer; a client may recover a cached
answer inside its public advance function. A terminal machine is padded with
unused row labels, so every positive-length probability experiment has the
same fixed depth. The state trace records states before their responses.
-/

noncomputable section

namespace NCConcave16991.DenseWeakHiding.FreshCompiler

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev Reply (D : ℕ) := Fin D → Fin 2
def zeroReply (D : ℕ) : Reply D := fun _ ↦ 0

structure Context (S : Type*) (n : ℕ) where
  fuel : ℕ
  state : S
  seen : Finset (Fin n)
  trace : List S

variable {S : Type*} {n D : ℕ}
  (request : S → Option (Fin n)) (advance : S → Reply D → S)

def seek : ℕ → S → ℕ × S
  | 0,s => (0,s)
  | fuel + 1,s =>
      match request s with
      | some _ => (fuel + 1,s)
      | none => seek fuel (advance s (zeroReply D))

def seekTrace : ℕ → S → List S
  | 0,s => [s]
  | fuel + 1,s =>
      s :: (match request s with
        | some _ => []
        | none => seekTrace fuel (advance s (zeroReply D)))

theorem seek_fuel_le (fuel : ℕ) (s : S) : (seek request advance fuel s).1 ≤ fuel := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases h : request s with
      | none => simpa only [seek,h] using (ih (advance s (zeroReply D))).trans (Nat.le_succ fuel)
      | some i => simp [seek,h]

theorem seek_positive_request (fuel : ℕ) (s : S)
    (hf : 0 < (seek request advance fuel s).1) :
    ∃ i, request (seek request advance fuel s).2 = some i := by
  induction fuel generalizing s with
  | zero => simp [seek] at hf
  | succ fuel ih =>
      cases h : request s with
      | none =>
          simp only [seek,h] at hf ⊢
          exact ih (advance s (zeroReply D)) hf
      | some i => exact ⟨i,by simp [seek,h]⟩

def freshRequest (c : Context S n) : Option (Fin n) :=
  let z := seek request advance c.fuel c.state
  if z.1 = 0 then none else
    match request z.2 with
    | none => none
    | some i => if i ∈ c.seen then none else some i

theorem freshRequest_not_mem (c : Context S n) (i : Fin n)
    (hi : freshRequest request advance c = some i) : i ∉ c.seen := by
  dsimp only [freshRequest] at hi
  by_cases hz : (seek request advance c.fuel c.state).1 = 0
  · simp only [hz,ite_true] at hi
    contradiction
  · rw [if_neg hz] at hi
    cases hreq : request (seek request advance c.fuel c.state).2 with
    | none => simp only [hreq] at hi; contradiction
    | some j =>
        by_cases hj : j ∈ c.seen
        · simp only [hreq,hj,ite_true] at hi
          contradiction
        · have he : j = i := by simpa only [hreq,hj,ite_false,Option.some.injEq] using hi
          subst i
          exact hj

def unused (hn : 0 < n) (A : Finset (Fin n)) : Fin n :=
  if h : ∃ i, i ∉ A then Classical.choose h else ⟨0,hn⟩

theorem unused_not_mem (hn : 0 < n) (A : Finset (Fin n)) (hA : A.card < n) :
    unused hn A ∉ A := by
  have he : ∃ i : Fin n, i ∉ A := by
    by_contra h
    have ha : A = Finset.univ := by
      ext i
      simp only [Finset.mem_univ, iff_true]
      exact Classical.not_not.mp (fun hi ↦ h ⟨i,hi⟩)
    rw [ha, Finset.card_univ, Fintype.card_fin] at hA
    omega
  exact by simpa only [unused, dif_pos he] using Classical.choose_spec he

def pick (hn : 0 < n) (c : Context S n) : Fin n :=
  (freshRequest request advance c).getD (unused hn c.seen)

theorem pick_not_mem (hn : 0 < n) (c : Context S n) (hc : c.seen.card < n) :
    pick request advance hn c ∉ c.seen := by
  cases h : freshRequest request advance c with
  | none => simpa [pick,h] using unused_not_mem hn c.seen hc
  | some i => simpa [pick,h] using freshRequest_not_mem request advance c i h

def consume (hn : 0 < n) (c : Context S n) (answer : Reply D) : Context S n :=
  let z := seek request advance c.fuel c.state
  let active := freshRequest request advance c
  { fuel := if active.isSome then z.1 - 1 else 0
    state := if active.isSome then advance z.2 answer else z.2
    seen := insert (pick request advance hn c) c.seen
    trace := c.trace ++ (if active.isSome then seekTrace request advance c.fuel c.state
      else (seekTrace request advance c.fuel c.state).dropLast) }

def initial (fuel : ℕ) (s : S) : Context S n := ⟨fuel,s,∅,[]⟩

def context (hn : 0 < n) (fuel : ℕ) (s : S) :
    (t : ℕ) → (Fin t → Reply D) → Context S n
  | 0,_ => initial fuel s
  | t + 1,h => consume request advance hn (context hn fuel s t (Fin.init h)) (h (Fin.last t))

def nextRow (hn : 0 < n) (fuel : ℕ) (s : S) (t : ℕ) (h : Fin t → Reply D) : Fin n :=
  pick request advance hn (context request advance hn fuel s t h)

def recoveredTrace (hn : 0 < n) (fuel : ℕ) (s : S) (t : ℕ) (h : Fin t → Reply D) : List S :=
  let c := context request advance hn fuel s t h
  c.trace ++ seekTrace request advance c.fuel c.state

theorem context_seen_card_le (hn : 0 < n) (fuel : ℕ) (s : S)
    (t : ℕ) (h : Fin t → Reply D) :
    (context request advance hn fuel s t h).seen.card ≤ t := by
  induction t with
  | zero => simp [context, initial]
  | succ t ih =>
      change (insert _ (context request advance hn fuel s t (Fin.init h)).seen).card ≤ t + 1
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (ih (Fin.init h)) 1)

theorem context_seen_eq_observed (hn : 0 < n) (fuel : ℕ) (s : S)
    (t : ℕ) (h : Fin t → Reply D) :
    (context request advance hn fuel s t h).seen =
      (RowExperiment.policyExperiment (nextRow request advance hn fuel s) t).observedRows h := by
  induction t with
  | zero => simp [context,initial,RowExperiment.policyExperiment,RowExperiment.observedRows]
  | succ t ih =>
      rw [RowExperiment.observedRows_policy_succ]
      change insert (nextRow request advance hn fuel s t (Fin.init h))
        (context request advance hn fuel s t (Fin.init h)).seen = _
      rw [ih]

/-- Freshness is guaranteed on every formal response history, including null
histories. It does not need an oracle-distribution premise. -/
theorem nextRow_fresh (hn : 0 < n) (fuel : ℕ) (s : S) (t : ℕ)
    (h : Fin t → Reply D) (ht : t < n) :
    nextRow request advance hn fuel s t h ∉
      (RowExperiment.policyExperiment (nextRow request advance hn fuel s) t).observedRows h := by
  rw [← context_seen_eq_observed]
  exact pick_not_mem request advance hn _ ((context_seen_card_le request advance hn fuel s t h).trans_lt ht)

/-- Predetermined initialization is represented as one ordinary row read, so
it is included in the information budget. -/
def initializedRequest (i₀ : Fin n) : Unit ⊕ S → Option (Fin n)
  | .inl _ => some i₀
  | .inr s => request s

def initializedAdvance (start : Reply D → S) : Unit ⊕ S → Reply D → Unit ⊕ S
  | .inl _,a => .inr (start a)
  | .inr s,a => .inr (advance s a)

end NCConcave16991.DenseWeakHiding.FreshCompiler
