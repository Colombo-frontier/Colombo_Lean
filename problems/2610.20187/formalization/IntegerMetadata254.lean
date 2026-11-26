import ScheduledRationalTransition254

namespace Paper254

/-- Binary logarithm by repeated integer division. The counter records one
comparison per call and one division plus one increment per recursive step. -/
def countedLogTwo (n : ℕ) : ℕ×ℕ :=
  if h : n<2 then (0,1) else
    let out:=countedLogTwo (n/2)
    (out.1+1,out.2+3)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem countedLogTwo_spec (n : ℕ) : countedLogTwo n=(Nat.log 2 n,3*Nat.log 2 n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    rw [countedLogTwo]
    split_ifs with hn
    · rw [Nat.log_of_lt hn]
    · have hlt : n/2<n := Nat.div_lt_self (by omega) (by decide)
      rw [ih (n/2) hlt,Nat.log_of_one_lt_of_le (by decide : 1<(2:ℕ)) (by omega : 2≤n)]
      congr 1

def depth_countedActiveTest (h t i : ℕ) : Bool×ℕ :=
  let tests:=countedAny (fun k=>let p:=countedNatPowTwo k
    (decide (i%p.1=0 ∧ t-i≤4*p.1),p.2+5)) (List.range h)
  (decide (1 ≤ i ∧ i ≤ t) && tests.1,tests.2+2)

def depth_countedCandidateList (h t : ℕ) : List ℕ×ℕ :=
  mapWithCosts (fun kq : ℕ×ℕ=>let p:=countedNatPowTwo kq.1
    (t-(p.1*kq.2+t%p.1),p.2+4)) ((List.range h).product (List.range 5))

def depth_countedShortHistoryList (h t : ℕ) : List ℕ×ℕ :=
  let candidates:=depth_countedCandidateList h t
  let active:=countedFilter (depth_countedActiveTest h t) candidates.1
  let sorted:=countedUniqueSort active.1
  (sorted.1,candidates.2+active.2+sorted.2)

def depth_countedNumberedLive (h T K t : ℕ) : List (Fin ((T+1)*(K+1)))×ℕ :=
  let histories:=depth_countedShortHistoryList h t
  let expanded:=countedFlatMap (countedHistoryKeys T K) histories.1
  let sorted:=countedUniqueSort expanded.1
  (sorted.1,histories.2+expanded.2+sorted.2)

theorem depth_countedNumberedLive_program (T K t : ℕ) :
    depth_countedNumberedLive (Nat.log 2 t+1) T K t=countedNumberedLive T K t := rfl

def fullyCountedStandardLive (T K t : ℕ) : List (Fin ((T+1)*(K+1)))×ℕ :=
  let clock:=min t T+1
  let depth:=countedLogTwo clock
  let out:=depth_countedNumberedLive (depth.1+1) T K clock
  (out.1,depth.2+out.2+3)

theorem fullyCountedStandardLive_program (T K t : ℕ) :
    (fullyCountedStandardLive T K t).1=((standardRationalSchedule T K).live t).sort (·≤·) := by
  simp only [fullyCountedStandardLive,countedLogTwo_spec,depth_countedNumberedLive_program]
  exact countedStandardLive_value T K t

theorem fullyCountedStandardLive_cost (T K t : ℕ) :
    (fullyCountedStandardLive T K t).2≤
      shortMetadataBound (Nat.log 2 (T+1)+1) K+3*Nat.log 2 (T+1)+4 := by
  have hc:=countedNumberedLive_cost T K (min t T+1)
  have hm : Nat.log 2 (min t T+1)≤Nat.log 2 (T+1) := Nat.log_mono_right (by omega)
  have hb:=shortMetadataBound_mono (K:=K) (Nat.add_le_add_right hm 1)
  simp only [fullyCountedStandardLive,countedLogTwo_spec,depth_countedNumberedLive_program]
  omega

/-- All dynamic keys fit into a word polynomial in the horizon and number of
scales. Comparisons and arithmetic on these words therefore have polynomial
bit cost in log(T+1)+log(K+1) under the integer primitive model. -/
def metadataWordBound (T K : ℕ) : ℕ := 8*(T+1)*(K+1)

theorem metadata_candidate_operands (T K t k q : ℕ) (ht : t≤T+1)
    (hk : k<Nat.log 2 t+1) (hq : q<5) :
    2^k≤metadataWordBound T K ∧
    2^k*q+t%2^k≤metadataWordBound T K ∧
    4*2^k≤metadataWordBound T K := by
  have hp' : 2^k≤T+1 := by
    by_cases hz : t=0
    · subst t
      have hk0 : k=0 := by simpa using hk
      subst k
      simp
    · exact (Nat.pow_le_of_le_log hz (by omega : k≤Nat.log 2 t)).trans ht
  have hmod : t%2^k≤t := Nat.mod_le _ _
  have hq' : q≤4 := by omega
  have hprod:=Nat.mul_le_mul hp' hq'
  have hbase : 8*(T+1)≤metadataWordBound T K := by
    unfold metadataWordBound
    nlinarith
  constructor
  · omega
  · constructor <;> nlinarith

theorem metadata_numbered_key (T K : ℕ) (e : Fin ((T+1)*(K+1))) :
    e.val<metadataWordBound T K := by
  have he:=e.isLt
  unfold metadataWordBound
  nlinarith

end Paper254
#print axioms Paper254.fullyCountedStandardLive_program
#print axioms Paper254.fullyCountedStandardLive_cost
#print axioms Paper254.metadata_candidate_operands
