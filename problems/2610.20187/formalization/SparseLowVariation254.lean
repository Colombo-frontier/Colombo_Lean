import SparseBranches254

noncomputable section
namespace Paper254

section Trajectory
variable {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
  (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
  (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d)

local notation "lam" => curvature D G η/2
local notation "a₀" => masterOverhead T K lam

theorem sparse_low_variation (hf : ∀ t < T, AdmissibleLoss W G η (f t))
    (k : Fin (K+1)) (u : ℕ → W.carrier) (L : ℕ) (hL : 1 ≤ L) (hpow : T < 2^L)
    (start n₀ : ℕ) (hn : 0 < n₀) (hend : start+n₀ ≤ T)
    (hvar : intervalCharge (fun t => ‖(u (t+1)).val-(u t).val‖) start (n₀-1) ≤
      variationThreshold L a₀ (birthBudget d D (q k)) lam (q k)) :
    intervalCharge (actualComparatorDifference (T := T) W hD hG hη w0 q hq f k u) start n₀ ≤
      restartThreshold L a₀ (birthBudget d D (q k)) lam/64 := by
  let B := birthBudget d D (q k)
  let H := restartThreshold L a₀ B lam
  let C := H/(64*L)
  let delta := fun t => ‖(u (t+1)).val-(u t).val‖
  let r := actualComparatorDifference (T := T) W hD hG hη w0 q hq f k u
  let shifted := fun t => r (start+t)
  have hlam : 0 < lam := div_pos (curvature_pos D G η hD hG hη) (by norm_num)
  have ha := masterOverhead_nonneg T K lam hlam
  have hB : 0 ≤ B := birthBudget_nonneg d D (q k) hD (hq k)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLp : (0 : ℝ) < L := by linarith
  have hH : 0 ≤ H := by dsimp [H, restartThreshold]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have haH : 128*a₀ ≤ H := by
    have hratio : 0 ≤ B/lam := div_nonneg hB hlam.le
    dsimp [H, restartThreshold]
    nlinarith [mul_nonneg (show 0 ≤ (L : ℝ)-1 by linarith) ha,
      mul_nonneg hLp.le hratio]
  have hpay : 2*C*L ≤ H-a₀ := by
    have he : 2*C*L = H/32 := by dsimp [C]; field_simp; ring
    rw [he]
    linarith
  have hcase : ∀ b n, 0 < n → b+n ≤ n₀ → ∃ left, 2*left < n ∧
      (intervalCharge shifted (b+left) (n-left) ≤ C ∨
        ∃ j, 0 < j ∧ j ≤ n-left ∧ intervalCharge shifted (b+left) j ≤ -(H-a₀)) := by
    intro b n hnpos hnend
    obtain ⟨i, hstart, hmid, hactive⟩ := streaming_history_cover
      (start+b+1) (start+b+n) (by omega) (by omega)
    have hi : 0 < i := by omega
    have hiT : i-1 < T+1 := by have hh := hactive.2.1; omega
    let e : HistoryExpert T K := (⟨i-1, hiT⟩, k)
    let left := i-1-(start+b)
    have hid : e.1.val = start+b+left := by dsimp [e, left]; omega
    have hbirth : expertBirth e = i := by dsimp [expertBirth, e]; omega
    have hleft : 2*left < n := by dsimp [left]; omega
    have hsuffix : 0 < n-left := by omega
    have hsuffixEq : n-left-1+1 = n-left := by omega
    have hlast : e.1.val+(n-left-1)+1 = start+b+n := by omega
    have heactive : HistoryActive (e.1.val+(n-left-1)+1) (expertBirth e) := by
      rw [hlast, hbirth]
      exact hactive
    have heT : e.1.val+(n-left-1) < T := by omega
    have hp : intervalCharge delta e.1.val (n-left-1) ≤
        variationThreshold L a₀ B lam (q k) := by
      exact le_trans (intervalCharge_subinterval_le delta (fun _ => norm_nonneg _)
        start (n₀-1) e.1.val (n-left-1) (by omega) (by omega)) hvar
    refine ⟨left, hleft, ?_⟩
    by_cases hdraw : ∀ j ≤ n-left, -H ≤
        intervalCharge (actualHistoryDifference W hD hG hη w0 q hq f e u) e.1.val j
    · left
      have hg := sparse_good_suffix W hD hG hη w0 q hq f hf e u (n-left-1) L hLr heT heactive hp
        (by simpa only [hsuffixEq] using hdraw)
      rw [hsuffixEq] at hg
      change intervalCharge (fun t => r (start+t)) (b+left) (n-left) ≤ C
      rw [intervalCharge_shift, show start+(b+left) = e.1.val by omega]
      exact hg
    · right
      push_neg at hdraw
      obtain ⟨j, hjlen, hjbad⟩ := hdraw
      have hjpos : 0 < j := by
        by_contra hh
        have hj0 : j = 0 := by omega
        subst j
        simp only [intervalCharge, Finset.range_zero, Finset.sum_empty] at hjbad
        linarith
      have hjactive : HistoryActive (e.1.val+j) (expertBirth e) :=
        historyActive_prefix heactive (by dsimp [expertBirth]; omega) (by omega)
      have hb := sparse_bad_prefix W hD hG hη w0 q hq f hf e u j H hjpos (by omega) hjactive hjbad.le
      refine ⟨j, hjpos, hjlen, ?_⟩
      change intervalCharge (fun t => r (start+t)) (b+left) j ≤ -(H-a₀)
      rw [intervalCharge_shift, show start+(b+left) = e.1.val by omega]
      change intervalCharge r e.1.val j ≤ a₀-H at hb
      linarith
  have hh := interval_restart_bound shifted n₀ L C (H-a₀) hC hpay hcase 0 n₀ L
    (by omega) le_rfl (by omega)
  have he : C*L = H/64 := by dsimp [C]; field_simp
  rw [he] at hh
  change intervalCharge (fun t => r (start+t)) 0 n₀ ≤ H/64 at hh
  rw [intervalCharge_shift, Nat.add_zero] at hh
  exact hh

end Trajectory
end Paper254
#print axioms Paper254.sparse_low_variation
