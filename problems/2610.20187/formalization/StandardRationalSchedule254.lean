import RationalSparseRun254
import ComputationalCost254

open scoped BigOperators
namespace Paper254

def numberedExpertEquiv (T K : ℕ) : HistoryExpert T K ≃ Fin ((T+1)*(K+1)) :=
  finProdFinEquiv

def numberedBirthPrior (T K : ℕ) (i : Fin (T+1)) (e : Fin ((T+1)*(K+1))) : ℚ :=
  if ((numberedExpertEquiv T K).symm e).1=i then 1/(K+1:ℚ) else 0

def standardRationalSchedule (T K : ℕ) : RationalSparseSchedule ((T+1)*(K+1)) where
  live t := (shortLiveExperts T K (min t T+1)).map (numberedExpertEquiv T K).toEmbedding
  prior t := numberedBirthPrior T K ⟨min (t+1) T,by omega⟩
  share t := 1/(t+2:ℚ)

theorem numberedBirthPrior_total (T K : ℕ) (i : Fin (T+1)) :
    (∑ e,numberedBirthPrior T K i e)=1 := by
  rw [←(numberedExpertEquiv T K).sum_comp (numberedBirthPrior T K i)]
  simp only [numberedBirthPrior,Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp [show (K:ℚ)+1≠0 by positivity]

theorem numberedBirthPrior_nonneg (T K : ℕ) (i : Fin (T+1))
    (e : Fin ((T+1)*(K+1))) : 0≤numberedBirthPrior T K i e := by
  dsimp [numberedBirthPrior]
  split_ifs <;> positivity

theorem numberedBirthPrior_live (T K : ℕ) (i : Fin (T+1))
    (e : Fin ((T+1)*(K+1))) (he : 0<numberedBirthPrior T K i e) :
    (numberedExpertEquiv T K).symm e∈shortLiveExperts T K (i.val+1) := by
  have hi : ((numberedExpertEquiv T K).symm e).1=i := by
    by_contra hn
    simp [numberedBirthPrior,hn] at he
  rw [shortLiveExperts_eq,mem_liveExperts]
  simp only [expertBirth,hi]
  exact historyActive_birth _ (by omega)

set_option maxHeartbeats 800000 in
theorem standardRationalSchedule_spec (T K : ℕ) :
    RationalSparseScheduleSpec (standardRationalSchedule T K) := by
  constructor
  · intro t e
    exact numberedBirthPrior_nonneg T K _ e
  · intro t
    exact numberedBirthPrior_total T K _
  · intro t e he
    let i : Fin (T+1) := ⟨min (t+1) T,by omega⟩
    have hb : 0<numberedBirthPrior T K i e := he
    have hl := numberedBirthPrior_live T K i e hb
    change e∈Finset.map (numberedExpertEquiv T K).toEmbedding
      (shortLiveExperts T K (min (t+1) T+1))
    apply Finset.mem_map.mpr
    exact ⟨(numberedExpertEquiv T K).symm e,hl,
      (numberedExpertEquiv T K).apply_symm_apply e⟩
  · intro t
    dsimp [standardRationalSchedule]
    positivity
  · intro t
    change 1/(t+2:ℚ)≤1
    apply (div_le_one (by positivity)).mpr
    have ht : (0:ℚ)≤t := by positivity
    linarith

theorem standardRationalSchedule_live {T K t : ℕ} (ht : t≤T)
    (e : HistoryExpert T K) :
    numberedExpertEquiv T K e∈(standardRationalSchedule T K).live t ↔
      HistoryActive (t+1) (expertBirth e) := by
  change _∈Finset.map (numberedExpertEquiv T K).toEmbedding (shortLiveExperts T K (min t T+1))↔_
  rw [Nat.min_eq_left ht,Finset.mem_map_equiv,shortLiveExperts_eq,mem_liveExperts]
  rw [Equiv.symm_apply_apply]

theorem standardRationalSchedule_birth {T K t : ℕ} (ht : t<T) (k : Fin (K+1)) :
    (standardRationalSchedule T K).prior t (numberedExpertEquiv T K (⟨t+1,by omega⟩,k))=
      1/(K+1:ℚ) := by
  simp [standardRationalSchedule,numberedBirthPrior,Nat.min_eq_left (by omega : t+1≤T)]

theorem standardRationalSchedule_card (T K t : ℕ) :
    ((standardRationalSchedule T K).live t).card≤5*(Nat.log 2 (min t T+1)+1)*(K+1) := by
  change (Finset.map _ _).card≤_
  rw [Finset.card_map]
  exact shortLiveExperts_card T K _

end Paper254
#print axioms Paper254.standardRationalSchedule_spec
#print axioms Paper254.standardRationalSchedule_live
#eval ((Paper254.standardRationalSchedule 1000 9).live 999).card
