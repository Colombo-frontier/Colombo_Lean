import SparseCounts254

namespace Paper254

/-- A bounded candidate list: five predecessors at each dyadic depth. -/
def shortHistoryCandidates (t : ℕ) : Finset ℕ :=
  ((Finset.range (Nat.log 2 t+1)) ×ˢ (Finset.range 5)).image
    (fun k=>t-(2^k.1*k.2+t%2^k.1))

def boundedHistoryActive (t i : ℕ) : Prop :=
  1 ≤ i ∧ i ≤ t ∧ ∃ k∈Finset.range (Nat.log 2 t+1),
    i%2^k=0 ∧ t-i≤4*2^k

instance (t i : ℕ) : Decidable (boundedHistoryActive t i) := by
  unfold boundedHistoryActive
  infer_instance

theorem boundedHistoryActive_iff (t i : ℕ) : boundedHistoryActive t i↔HistoryActive t i := by
  constructor
  · rintro ⟨hi,hit,k,hk,hdiv,hgap⟩
    exact ⟨hi,hit,hgap.trans (historyLifetime_dvd_lower hi (Nat.dvd_of_mod_eq_zero hdiv))⟩
  · intro hi
    let k:=padicValNat 2 i
    have hpow : 2^k≤t := (Nat.le_of_dvd hi.1 (pow_padicValNat_dvd (p:=2) (n:=i))).trans hi.2.1
    have hk : k<Nat.log 2 t+1 := by
      have hh:=Nat.le_log_of_pow_le (by norm_num : 1<(2:ℕ)) hpow
      omega
    refine ⟨hi.1,hi.2.1,k,Finset.mem_range.mpr hk,Nat.mod_eq_zero_of_dvd (pow_padicValNat_dvd (p:=2) (n:=i)),?_⟩
    simpa [historyLifetime,pow_add,Nat.mul_comm,k] using hi.2.2

def shortActiveHistories (t : ℕ) : Finset ℕ :=
  (shortHistoryCandidates t).filter (boundedHistoryActive t)

theorem activeHistory_in_shortCandidates (t i : ℕ) (hi : HistoryActive t i) :
    i∈shortHistoryCandidates t := by
  let k := padicValNat 2 i
  let q := (t-i)/2^k
  have hpow : 2^k≤t := (Nat.le_of_dvd hi.1 (pow_padicValNat_dvd (p:=2) (n:=i))).trans hi.2.1
  have hk : k<Nat.log 2 t+1 := by
    have hh := Nat.le_log_of_pow_le (by norm_num : 1<(2:ℕ)) hpow
    omega
  have hq : q<5 := by
    have hs : t-i ≤ 4*2^k := by simpa [historyLifetime,pow_add,Nat.mul_comm,k] using hi.2.2
    have hh := Nat.div_le_div_right (c:=2^k) hs
    have hp : 0<2^k := by positivity
    have hq4 : q≤4 := by simpa [q,Nat.mul_div_cancel,hp.ne'] using hh
    omega
  apply Finset.mem_image.mpr
  refine ⟨(k,q),Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk,Finset.mem_range.mpr hq⟩,?_⟩
  have hr := divisible_predecessor_reconstruct hi.2.1 (pow_padicValNat_dvd (p:=2) (n:=i))
  change t-(2^k*q+t%2^k)=i
  change i+2^k*q+t%2^k=t at hr
  omega

theorem shortActiveHistories_eq (t : ℕ) : shortActiveHistories t=activeHistories t := by
  ext i
  simp only [shortActiveHistories,Finset.mem_filter,mem_activeHistories]
  rw [boundedHistoryActive_iff]
  change (_ ∧ HistoryActive t i) ↔ HistoryActive t i
  exact ⟨And.right,fun hi=>⟨activeHistory_in_shortCandidates t i hi,hi⟩⟩

theorem shortHistoryCandidates_card (t : ℕ) :
    (shortHistoryCandidates t).card≤5*(Nat.log 2 t+1) := by
  have hh := Finset.card_image_le
    (s:=(Finset.range (Nat.log 2 t+1)) ×ˢ (Finset.range 5))
    (f:=fun k : ℕ×ℕ=>t-(2^k.1*k.2+t%2^k.1))
  simpa only [shortHistoryCandidates,Finset.card_product,Finset.card_range,Nat.mul_comm] using hh

/-- Enumerate scale entries only for the bounded candidate history list. -/
def shortLiveExperts (T K t : ℕ) : Finset (HistoryExpert T K) :=
  (shortActiveHistories t).biUnion (fun i=>
    if h : 0 < i ∧ i ≤ T+1 then
      (Finset.univ : Finset (Fin (K+1))).image (fun k=>(⟨i-1,by omega⟩,k))
    else ∅)

theorem shortLiveExperts_eq (T K t : ℕ) : shortLiveExperts T K t=liveExperts T K t := by
  ext e
  rw [shortLiveExperts,Finset.mem_biUnion,mem_liveExperts,shortActiveHistories_eq]
  constructor
  · rintro ⟨i,hi,he⟩
    split_ifs at he with h
    · obtain ⟨k,_,hk⟩ := Finset.mem_image.mp he
      have heq := congrArg (fun z : HistoryExpert T K=>z.1.val) hk
      have hb : expertBirth e=i := by dsimp [expertBirth]; simp only at heq; omega
      rw [hb]
      exact (mem_activeHistories t i).mp hi
    · simp at he
  · intro he
    refine ⟨expertBirth e,(mem_activeHistories t _).mpr he,?_⟩
    have h : 0<expertBirth e ∧ expertBirth e≤T+1 := by dsimp [expertBirth]; omega
    rw [dif_pos h]
    apply Finset.mem_image.mpr
    refine ⟨e.2,Finset.mem_univ _,?_⟩
    apply Prod.ext
    · apply Fin.ext
      simp [expertBirth]
    · rfl

theorem shortLiveExperts_card (T K t : ℕ) :
    (shortLiveExperts T K t).card≤5*(Nat.log 2 t+1)*(K+1) := by
  rw [shortLiveExperts_eq]
  exact liveExperts_card T K t

end Paper254
#print axioms Paper254.shortLiveExperts_eq
#eval (Paper254.shortActiveHistories 1000).sort (· ≤ ·)
