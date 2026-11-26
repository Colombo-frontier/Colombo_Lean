import AnytimeMain254
import ExplicitRate254

noncomputable section
open scoped BigOperators
namespace Paper254

def curvedDoublingFamily {d : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier) :
    (H : ℕ) → OnlineLearner W H :=
  fun _ => dyadicLearner W hD hG hη w0

theorem curved_prefix_clipped {d H m : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
    (hm0 : 0 < m) (hm : m ≤ H) (f : Fin m → Loss d)
    (hf : ∀ t,AdmissibleLoss W G η (f t)) (u : Fin m → W.carrier)
    (τ : ℝ) (hτ : 0 < τ) (hτD : τ ≤ D) :
    regret (prefixLearner (curvedDoublingFamily W hD hG hη w0 H) hm) f u ≤
      2048*((d+1 : ℝ)*logFactor H^2/curvature D G η+
        Real.sqrt (d+1 : ℝ)*logFactor H^2/(curvature D G η*τ)*pathLength u+
        curvature D G η*G^2*((H : ℝ)*τ^2+D^2/H)) := by
  have hH : 0 < H := lt_of_lt_of_le hm0 hm
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hslo : D/H ≤ max τ (D/H) := le_max_right _ _
  have hshi : max τ (D/H) ≤ D := max_le hτD ((div_le_self hD.le hH1))
  have hh := dyadic_learner_clipped W hD hG hη hH w0
    (paddedLoss f) (padded_admissible W hG.le f hf) (paddedComparator hm0 u)
    (max τ (D/H)) hslo hshi
  rw [prefix_regret _ hm hm0 f u,padded_pathLength hm hm0 u] at hh
  have hγ := curvature_pos D G η hD hG hη
  have hp := pathLength_nonneg u
  have hdv := div_le_div_of_nonneg_left
    (show 0 ≤ Real.sqrt (d+1 : ℝ)*logFactor H^2 by positivity)
    (mul_pos hγ hτ) (mul_le_mul_of_nonneg_left (le_max_left τ (D/H)) hγ.le)
  have hmove := mul_le_mul_of_nonneg_right hdv hp
  have hsm := mul_le_mul_of_nonneg_left (epoch_clipped_smoothing H D τ hHr hD.le hτ.le)
    (show 0 ≤ curvature D G η*G^2 by positivity)
  dsimp [curvedDoublingFamily]
  nlinarith

theorem dyadic_reciprocal_sum (J : ℕ) :
    (∑ j : Fin J,(1 : ℝ)/(2:ℝ)^j.val) ≤ 2 := by
  have hh := doubling_error_sum 2 (by norm_num) J
  have he : ∀ j : ℕ,(2:ℝ)/2^(j+1)=1/2^j := by
    intro j
    rw [pow_succ]
    field_simp
  simp_rw [he] at hh
  change (∑ j : Fin J,(fun n : ℕ => (1 : ℝ)/(2:ℝ)^n) j.val) ≤ 2
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => (1:ℝ)/(2:ℝ)^n) J]
  exact hh

/-- The same curved learner is restarted without knowing the terminal
horizon. A common comparison scale is clipped locally, not imposed on short epochs. -/
theorem curved_anytime_explicit {d T : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (hT : 0 < T) (w0 : W.carrier)
    (f : Fin T → Loss d) (hf : ∀ t,AdmissibleLoss W G η (f t))
    (u : Fin T → W.carrier) (τ : ℝ) (hτ : 0 < τ) (hτD : τ ≤ D) :
    regret (anytimeRestriction (doublingLearner (curvedDoublingFamily W hD hG hη w0)) T) f u ≤
      2048*((epochCount T : ℝ)*(d+1 : ℝ)*logFactor T^2/curvature D G η+
        Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G η*τ)*pathLength u+
        curvature D G η*G^2*(2*T*τ^2+2*D^2)) := by
  let γ := curvature D G η
  let A := (d+1 : ℝ)*logFactor T^2/γ
  let B := Real.sqrt (d+1 : ℝ)*logFactor T^2/(γ*τ)
  let H : Fin (epochCount T) → ℝ := fun j => (2^j.val : ℕ)
  let P := fun j : Fin (epochCount T) => pathLength (epochComparator u j)
  have hγ : 0 < γ := curvature_pos D G η hD hG hη
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsumH : (∑ j,H j) ≤ 2*T := by
    dsimp [H]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [Fin.sum_univ_eq_sum_range]
    exact doubling_planned_time T hT
  have hsumR : (∑ j,1/H j) ≤ 2 := by simpa [H] using dyadic_reciprocal_sum (epochCount T)
  have hsumP : (∑ j,P j) ≤ pathLength u := epoch_path_sum u
  rw [doubling_regret_decomposition]
  have hlocal : ∀ j : Fin (epochCount T),
      regret (prefixLearner (curvedDoublingFamily W hD hG hη w0 (2^j.val)) (min_le_left _ _))
        (epochLoss f j) (epochComparator u j) ≤ 2048*(A+B*P j+γ*G^2*(H j*τ^2+D^2/H j)) := by
    intro j
    have hh := curved_prefix_clipped W hD hG hη w0 (epoch_length_pos hT j) (min_le_left _ _)
      (epochLoss f j) (fun k => hf (epochRound ⟨j,k⟩)) (epochComparator u j) τ hτ hτD
    have hlog := logFactor_mono (by positivity : 0 < 2^j.val) (epoch_horizon_le hT j)
    have hlog0 : 0 ≤ logFactor (2^j.val) := (by norm_num : (0:ℝ) ≤ 1).trans
      (logFactor_ge_one (2^j.val) (by positivity))
    have hsq : logFactor (2^j.val)^2 ≤ logFactor T^2 := by nlinarith
    apply hh.trans
    dsimp [A,B,P,H,γ]
    gcongr
    exact pathLength_nonneg _
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlocal j)
  apply hh.trans
  have hmove := mul_le_mul_of_nonneg_left hsumP hB
  have htime := mul_le_mul_of_nonneg_right hsumH (sq_nonneg τ)
  have hfloor := mul_le_mul_of_nonneg_left hsumR (sq_nonneg D)
  have hsmooth := mul_le_mul_of_nonneg_left (add_le_add htime hfloor)
    (show 0 ≤ γ*G^2 by positivity)
  have hrewrite : (∑ j : Fin (epochCount T),D^2/H j)=D^2*(∑ j : Fin (epochCount T),1/H j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.sum_mul,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hrewrite]
  dsimp [A,B,γ] at *
  ring_nf at hmove hsmooth ⊢
  linarith

/-- The clipped anytime statement uses a universal constant and one
learner before both the horizon and the path budget are quantified. -/
def AnytimeClippedStatement : Prop :=
  ∃ C : ℝ,0 < C ∧ ∀ D G η : ℝ,0 < D → 0 < G → 0 < η →
  ∀ d : ℕ,0 < d → ∀ W : Domain d D,
  ∃ A : (t : ℕ) → (Fin t → Loss d) → W.carrier,
  ∀ T : ℕ,0 < T → ∀ f : Fin T → Loss d,
  (∀ t,AdmissibleLoss W G η (f t)) → ∀ u : Fin T → W.carrier,
    regret (anytimeRestriction A T) f u ≤ G*D*T ∧
    ∀ τ : ℝ,D/T ≤ τ → τ ≤ D →
      regret (anytimeRestriction A T) f u ≤ C*
        (((epochCount T : ℝ)+1)*(d+1 : ℝ)*logFactor T^2/curvature D G η+
          Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G η*τ)*pathLength u+
          curvature D G η*G^2*T*τ^2)

theorem main_anytime_clipped : AnytimeClippedStatement := by
  refine ⟨4096,by norm_num,?_⟩
  intro D G η hD hG hη d _hd W
  obtain ⟨w,hw⟩ := W.nonempty
  let w0 : W.carrier := ⟨w,hw⟩
  refine ⟨doublingLearner (curvedDoublingFamily W hD hG hη w0),?_⟩
  intro T hT f hf u
  refine ⟨linear_regret_bound _ f u hG.le hf,?_⟩
  intro τ hlo hhi
  have hTr : (0:ℝ) < T := by exact_mod_cast hT
  have hτ : 0 < τ := (div_pos hD hTr).trans_le hlo
  have hh := curved_anytime_explicit W hD hG hη hT w0 f hf u τ hτ hhi
  let γ := curvature D G η
  have hγ : 0 < γ := curvature_pos D G η hD hG hη
  have hg := curvature_times_radius D G η hD hG
  change γ*(G*D) ≤ 1/4 at hg
  have hg0 : 0 ≤ γ*(G*D) := by positivity
  have hsq : γ^2*G^2*D^2 ≤ 1/16 := by nlinarith
  have hL := logFactor_ge_one T hT
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have ha : γ*G^2*D^2 ≤ (d+1 : ℝ)*logFactor T^2/γ := by
    apply (le_div_iff₀ hγ).mpr
    nlinarith [mul_nonneg hd0 (sq_nonneg (logFactor T))]
  have hm : 0 ≤ Real.sqrt (d+1 : ℝ)*logFactor T^2/(γ*τ)*pathLength u := by
    exact mul_nonneg (by positivity) (pathLength_nonneg _)
  have hj : 0 ≤ (epochCount T : ℝ)*((d+1 : ℝ)*logFactor T^2/γ) := by positivity
  change _ ≤ 4096*(((epochCount T : ℝ)+1)*(d+1 : ℝ)*logFactor T^2/γ+
    Real.sqrt (d+1 : ℝ)*logFactor T^2/(γ*τ)*pathLength u+γ*G^2*T*τ^2)
  change _ ≤ 2048*((epochCount T : ℝ)*(d+1 : ℝ)*logFactor T^2/γ+
    Real.sqrt (d+1 : ℝ)*logFactor T^2/(γ*τ)*pathLength u+γ*G^2*(2*T*τ^2+2*D^2)) at hh
  ring_nf at hh ha hm hj ⊢
  linarith

end Paper254
#print axioms Paper254.curved_anytime_explicit
#print axioms Paper254.main_anytime_clipped
