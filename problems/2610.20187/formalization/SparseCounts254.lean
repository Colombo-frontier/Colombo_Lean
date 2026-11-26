import SparseMaster254
import LogBudget254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem liveExperts_card (T K t : ℕ) :
    (liveExperts T K t).card ≤ 5*(Nat.log 2 t+1)*(K+1) := by
  classical
  let f := fun e : HistoryExpert T K => (expertBirth e,e.2)
  let target := (activeHistories t) ×ˢ (Finset.univ : Finset (Fin (K+1)))
  have hmap : Set.MapsTo f (liveExperts T K t) target := by
    intro e he
    exact Finset.mem_product.mpr ⟨(mem_activeHistories _ _).mpr ((mem_liveExperts e).mp he), Finset.mem_univ _⟩
  have hinj : Set.InjOn f (liveExperts T K t) := by
    intro e _ j _ he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    apply Prod.ext
    · apply Fin.ext
      change e.1.val+1 = j.1.val+1 at h1
      omega
    · exact h2
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  have ha := Nat.mul_le_mul_right (K+1) (activeHistories_card t)
  simp only [target,Finset.card_product,Finset.card_univ,Fintype.card_fin] at hc
  exact hc.trans ha

theorem liveExperts_log_bound (T t : ℕ) (hT : 0 < T) (ht : t ≤ T) :
    ((liveExperts T (scaleCount T) t).card : ℝ) ≤ 20*logFactor T^2 := by
  have hc := liveExperts_card T (scaleCount T) t
  have hm : Nat.log 2 t ≤ Nat.log 2 T := Nat.log_mono_right ht
  have hh : (liveExperts T (scaleCount T) t).card ≤ 5*(scaleCount T+1)^2 := by
    dsimp [scaleCount] at *
    nlinarith
  have hreal : ((liveExperts T (scaleCount T) t).card : ℝ) ≤ 5*(scaleCount T+1 : ℝ)^2 := by
    exact_mod_cast hh
  have hlog := scaleDepth_log_bound T hT
  have hk0 : (0 : ℝ) ≤ scaleCount T+1 := by positivity
  have hL := logFactor_ge_one T hT
  nlinarith

/-- Storage in real scalar cells for the active Gaussian means, dense
precision matrices, and mixture weights. Indexing overhead is separate. -/
theorem active_gaussian_scalar_storage (d T t : ℕ) (hd : 0 < d) (hT : 0 < T) (ht : t ≤ T) :
    ((liveExperts T (scaleCount T) t).card : ℝ)*((d : ℝ)^2+d+1) ≤
      60*(d : ℝ)^2*logFactor T^2 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdim : (d : ℝ)^2+d+1 ≤ 3*(d : ℝ)^2 := by nlinarith
  have hc := liveExperts_log_bound T t hT ht
  have hh := mul_le_mul hc hdim (show 0 ≤ (d : ℝ)^2+d+1 by positivity)
    (show 0 ≤ 20*logFactor T^2 by positivity)
  nlinarith

end Paper254
#print axioms Paper254.active_gaussian_scalar_storage
