import NCConcave16991.DenseWeakFreshCompiler

/-! # Exact trace recovery for the actual bounded optional-row machine -/

noncomputable section

namespace NCConcave16991.DenseWeakHiding.FreshCompiler

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {S : Type*} {n D : ℕ}
  (request : S → Option (Fin n)) (advance : S → Reply D → S)

def execute (hn : 0 < n) (table : Fin n → Reply D) : ℕ → Context S n → Context S n
  | 0,c => c
  | t + 1,c => execute hn table t
      (consume request advance hn c (table (pick request advance hn c)))

theorem execute_succ_end (hn : 0 < n) (table : Fin n → Reply D) (t : ℕ) (c : Context S n) :
    execute request advance hn table (t + 1) c =
      consume request advance hn (execute request advance hn table t c)
        (table (pick request advance hn (execute request advance hn table t c))) := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => simpa only [execute] using ih (consume request advance hn c (table (pick request advance hn c)))

theorem context_actual_eq_execute {A : Type*} (read : A → Fin n → Fin 2) (bank : Fin D → A)
    (hn : 0 < n) (fuel : ℕ) (s : S) (t : ℕ) :
    context request advance hn fuel s t
      ((RowExperiment.policyExperiment (nextRow request advance hn fuel s) t).run read bank) =
    execute request advance hn (fun i d ↦ read (bank d) i) t (initial fuel s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [RowExperiment.run_policyExperiment_succ, context, Fin.init_snoc, Fin.snoc_last]
      rw [ih, execute_succ_end]
      simp only [nextRow,ih]

theorem self_mem_seekTrace (fuel : ℕ) (s : S) : s ∈ seekTrace request advance fuel s := by
  cases fuel <;> simp [seekTrace]

theorem seekTrace_length_fuel (fuel : ℕ) (s : S) :
    (seekTrace request advance fuel s).length + (seek request advance fuel s).1 = fuel + 1 := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases h : request s with
      | none =>
          have hi := ih (advance s (zeroReply D))
          simp only [seekTrace,seek,h,List.length_cons]
          omega
      | some i => simp only [seekTrace,seek,h,List.length_cons,List.length_nil]; omega

theorem seekTrace_dropLast_append (fuel : ℕ) (s : S) :
    (seekTrace request advance fuel s).dropLast ++ [(seek request advance fuel s).2] =
      seekTrace request advance fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases h : request s with
      | some i => simp [seekTrace,seek,h]
      | none =>
          simp only [seekTrace,seek,h]
          have hne : seekTrace request advance fuel (advance s (zeroReply D)) ≠ [] := by
            intro hz
            have hm := self_mem_seekTrace request advance fuel (advance s (zeroReply D))
            simp only [hz,List.not_mem_nil] at hm
          have hc : (s :: seekTrace request advance fuel (advance s (zeroReply D))).dropLast =
              s :: (seekTrace request advance fuel (advance s (zeroReply D))).dropLast := by
            cases he : seekTrace request advance fuel (advance s (zeroReply D)) with
            | nil => exact (hne he).elim
            | cons a l => rfl
          rw [hc,List.cons_append,ih]

theorem consume_potential_le (hn : 0 < n) (c : Context S n) (answer : Reply D) :
    (consume request advance hn c answer).trace.length + (consume request advance hn c answer).fuel ≤
      c.trace.length + c.fuel := by
  have hl := seekTrace_length_fuel request advance c.fuel c.state
  cases h : freshRequest request advance c with
  | none => simp only [consume,h,Option.isSome_none, Bool.false_eq_true,ite_false,List.length_append,List.length_dropLast]; omega
  | some i =>
      have hz : (seek request advance c.fuel c.state).1 ≠ 0 := by
        intro hz
        simp only [freshRequest,hz,ite_true] at h
        contradiction
      simp only [consume,h,Option.isSome_some,ite_true,List.length_append]
      omega

theorem context_potential_le (hn : 0 < n) (fuel : ℕ) (s : S) (t : ℕ) (h : Fin t → Reply D) :
    (context request advance hn fuel s t h).trace.length +
      (context request advance hn fuel s t h).fuel ≤ fuel := by
  induction t with
  | zero => simp [context,initial]
  | succ t ih =>
      have hp := consume_potential_le request advance hn
        (context request advance hn fuel s t (Fin.init h)) (h (Fin.last t))
      have hi := ih (Fin.init h)
      change (consume request advance hn (context request advance hn fuel s t (Fin.init h))
        (h (Fin.last t))).trace.length +
        (consume request advance hn (context request advance hn fuel s t (Fin.init h))
          (h (Fin.last t))).fuel ≤ fuel
      omega

/-- At most fuel+1 publicly reconstructed states need to be probed. -/
theorem recoveredTrace_length_le (hn : 0 < n) (fuel : ℕ) (s : S) (t : ℕ) (h : Fin t → Reply D) :
    (recoveredTrace request advance hn fuel s t h).length ≤ fuel + 1 := by
  have hp := context_potential_le request advance hn fuel s t h
  have hl := seekTrace_length_fuel request advance
    (context request advance hn fuel s t h).fuel (context request advance hn fuel s t h).state
  simp only [recoveredTrace,List.length_append]
  omega

/-- Actual states before responses, stopping before the response that would
exceed the selected-row quota. None transitions consume no selected row. -/
def cutTrace (table : Fin n → Reply D) : ℕ → ℕ → S → List S
  | 0,_,s => [s]
  | _ + 1,0,s => [s]
  | quota + 1,fuel + 1,s =>
      s :: (match request s with
        | none => cutTrace table (quota + 1) fuel (advance s (zeroReply D))
        | some i => cutTrace table quota fuel (advance s (table i)))

theorem cutTrace_seek_zero (table : Fin n → Reply D) (quota fuel : ℕ) (s x : S)
    (hz : (seek request advance fuel s).1 = 0)
    (hx : x ∈ cutTrace request advance table (quota + 1) fuel s) :
    x ∈ seekTrace request advance fuel s := by
  induction fuel generalizing s with
  | zero => simpa only [cutTrace,seekTrace] using hx
  | succ fuel ih =>
      cases h : request s with
      | some i => simp [seek,h] at hz
      | none =>
          simp only [seek,h] at hz
          simp only [cutTrace,h,List.mem_cons] at hx
          simp only [seekTrace,h,List.mem_cons]
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (ih (advance s (zeroReply D)) hz hx)

theorem cutTrace_seek_positive (table : Fin n → Reply D) (quota fuel : ℕ) (s x : S)
    (hp : 0 < (seek request advance fuel s).1) (i : Fin n)
    (hi : request (seek request advance fuel s).2 = some i)
    (hx : x ∈ cutTrace request advance table (quota + 1) fuel s) :
    x ∈ seekTrace request advance fuel s ∨
      x ∈ cutTrace request advance table quota ((seek request advance fuel s).1 - 1)
        (advance (seek request advance fuel s).2 (table i)) := by
  induction fuel generalizing s with
  | zero => simp [seek] at hp
  | succ fuel ih =>
      cases h : request s with
      | some j =>
          have he : j = i := Option.some.inj (by simpa only [seek,h] using hi)
          subst j
          simpa only [cutTrace,seekTrace,seek,h,List.mem_cons,List.mem_singleton,List.not_mem_nil,
            or_false,Nat.add_sub_cancel] using hx
      | none =>
          simp only [seek,h] at hp hi ⊢
          simp only [cutTrace,h,List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Or.inl (self_mem_seekTrace request advance _ _)
          · rcases ih (advance s (zeroReply D)) hp hi hx with hx | hx
            · exact Or.inl (by simpa only [seekTrace,h,List.mem_cons] using Or.inr hx)
            · exact Or.inr hx

theorem execute_trace_contains (hn : 0 < n) (table : Fin n → Reply D)
    (t : ℕ) (c : Context S n) (x : S) (hx : x ∈ c.trace) :
    x ∈ (execute request advance hn table t c).trace := by
  induction t generalizing c with
  | zero => exact hx
  | succ t ih =>
      apply ih
      exact List.mem_append.mpr (Or.inl hx)

theorem execute_zero_fields (hn : 0 < n) (table : Fin n → Reply D) (t : ℕ)
    (c : Context S n) (hc : c.fuel = 0) :
    (execute request advance hn table t c).fuel = 0 ∧
      (execute request advance hn table t c).state = c.state ∧
      (execute request advance hn table t c).trace = c.trace := by
  induction t generalizing c with
  | zero => exact ⟨hc,rfl,rfl⟩
  | succ t ih =>
      let c' := consume request advance hn c (table (pick request advance hn c))
      have hz : c'.fuel = 0 ∧ c'.state = c.state ∧ c'.trace = c.trace := by
        simp [c',consume,freshRequest,seek,seekTrace,hc]
      have hi := ih c' hz.1
      exact ⟨hi.1,hi.2.1.trans hz.2.1,hi.2.2.trans hz.2.2⟩

def FreshAlong (hn : 0 < n) (table : Fin n → Reply D) (c : Context S n) (r : ℕ) : Prop :=
  ∀ t < r, ∀ i,
    0 < (seek request advance (execute request advance hn table t c).fuel
      (execute request advance hn table t c).state).1 →
    request (seek request advance (execute request advance hn table t c).fuel
      (execute request advance hn table t c).state).2 = some i →
    i ∉ (execute request advance hn table t c).seen

/-- Every actual state before the row quota is exhausted is a public function
of the compiled finite transcript. This includes query-before-response states
and the terminal state when the bounded machine finishes earlier. -/
theorem cutTrace_subset_executeTrace (hn : 0 < n) (table : Fin n → Reply D)
    (r : ℕ) (c : Context S n) (hfresh : FreshAlong request advance hn table c r)
    (x : S) (hx : x ∈ cutTrace request advance table r c.fuel c.state) :
    x ∈ (execute request advance hn table r c).trace ++
      seekTrace request advance (execute request advance hn table r c).fuel
        (execute request advance hn table r c).state := by
  induction r generalizing c with
  | zero =>
      have he : x = c.state := by simpa only [cutTrace,List.mem_singleton] using hx
      subst x
      exact List.mem_append.mpr (Or.inr (self_mem_seekTrace request advance _ _))
  | succ r ih =>
      let z := seek request advance c.fuel c.state
      let c' := consume request advance hn c (table (pick request advance hn c))
      by_cases hz : z.1 = 0
      · have ha : freshRequest request advance c = none := by simp [freshRequest,hz,z]
        have hxseek := cutTrace_seek_zero request advance table r c.fuel c.state x hz hx
        rw [← seekTrace_dropLast_append request advance c.fuel c.state] at hxseek
        rcases List.mem_append.mp hxseek with hxdrop | hxlast
        · apply List.mem_append.mpr
          apply Or.inl
          apply execute_trace_contains request advance hn table r c' x
          simpa only [c',consume,ha,Option.isSome_none,Bool.false_eq_true,ite_false] using
            List.mem_append.mpr (Or.inr hxdrop : x ∈ c.trace ∨ x ∈ (seekTrace request advance c.fuel c.state).dropLast)
        · have he : x = z.2 := by simpa only [List.mem_singleton] using hxlast
          have hcfuel : c'.fuel = 0 := by simp [c',consume,ha]
          have hcstate : c'.state = z.2 := by simp [c',consume,ha,z]
          have hzero := execute_zero_fields request advance hn table r c' hcfuel
          apply List.mem_append.mpr
          apply Or.inr
          change x ∈ seekTrace request advance (execute request advance hn table r c').fuel
            (execute request advance hn table r c').state
          rw [hzero.1,hzero.2.1,hcstate]
          simpa only [seekTrace,List.mem_singleton] using he
      · have hp : 0 < z.1 := Nat.pos_of_ne_zero hz
        obtain ⟨i,hi⟩ := seek_positive_request request advance c.fuel c.state hp
        have hifresh : i ∉ c.seen := hfresh 0 (by omega) i hp hi
        have ha : freshRequest request advance c = some i := by
          simp only [freshRequest,hi,hifresh,ite_false]
          exact if_neg hz
        have htrace (y : S) (hy : y ∈ seekTrace request advance c.fuel c.state) :
            y ∈ (execute request advance hn table (r + 1) c).trace := by
          apply execute_trace_contains request advance hn table r c' y
          simpa only [c',consume,ha,Option.isSome_some,ite_true] using
            List.mem_append.mpr (Or.inr hy : y ∈ c.trace ∨ y ∈ seekTrace request advance c.fuel c.state)
        have hpi : pick request advance hn c = i := by simp [pick,ha]
        have hstate : c'.state = advance z.2 (table i) := by simp [c',consume,ha,hpi,z]
        have hfuel : c'.fuel = z.1 - 1 := by simp [c',consume,ha,z]
        have hnext : FreshAlong request advance hn table c' r := by
          intro t ht j hj hreq
          exact hfresh (t + 1) (by omega) j hj hreq
        rcases cutTrace_seek_positive request advance table r c.fuel c.state x hp i hi hx with hx | hx
        · exact List.mem_append.mpr (Or.inl (htrace x hx))
        · apply ih c' hnext
          simpa only [hstate,hfuel] using hx

theorem actual_cutTrace_subset_recovered {A : Type*} (read : A → Fin n → Fin 2)
    (bank : Fin D → A) (hn : 0 < n) (fuel : ℕ) (s : S) (r : ℕ)
    (hfresh : FreshAlong request advance hn (fun i d ↦ read (bank d) i) (initial fuel s) r)
    (x : S) (hx : x ∈ cutTrace request advance (fun i d ↦ read (bank d) i) r fuel s) :
    x ∈ recoveredTrace request advance hn fuel s r
      ((RowExperiment.policyExperiment (nextRow request advance hn fuel s) r).run read bank) := by
  have h := cutTrace_subset_executeTrace request advance hn (fun i d ↦ read (bank d) i)
    r (initial fuel s) hfresh x hx
  simpa only [recoveredTrace,context_actual_eq_execute] using h

end NCConcave16991.DenseWeakHiding.FreshCompiler
