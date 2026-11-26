import SignVector254
import FiniteInterface254

noncomputable section
open scoped BigOperators
namespace Paper254

def paddedSignVector {m d : ℕ} (θ : ℝ) (s : Fin m → Bool) : Space d :=
  WithLp.toLp 2 (fun j : Fin d => if hj : j.val < m then signedMean θ (s ⟨j.val,hj⟩) else 0)

theorem paddedSignVector_norm_sq {m d : ℕ} (hmd : m ≤ d) (θ : ℝ) (s : Fin m → Bool) :
    ‖paddedSignVector (d := d) θ s‖^2 = (m : ℝ)*θ^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have he : ∀ j : Fin d, ‖paddedSignVector (d := d) θ s j‖^2 = if j.val < m then θ^2 else 0 := by
    intro j
    change ‖(if hj : j.val < m then signedMean θ (s ⟨j.val,hj⟩) else 0)‖^2 = _
    split_ifs <;> simp [Real.norm_eq_abs,sq_abs,signedMean_sq]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hc : ((Finset.univ : Finset (Fin d)).filter (fun j => j.val < m)).card = m := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le hmd
  rw [hc]

def paddedSignInBall {m d : ℕ} (hmd : m ≤ d) (θ : ℝ) (hθ : (m : ℝ)*θ^2 ≤ 1/4)
    (s : Fin m → Bool) : (ballDomain d).carrier :=
  ⟨paddedSignVector θ s, by
    change paddedSignVector θ s ∈ Metric.closedBall 0 (1/2)
    rw [Metric.mem_closedBall, dist_zero_right]
    have hh := paddedSignVector_norm_sq hmd θ s
    have hn := norm_nonneg (paddedSignVector (d := d) θ s)
    nlinarith⟩

theorem paddedSign_norm_bound {m d : ℕ} (hmd : m ≤ d) (θ a : ℝ) (ha : 0 ≤ a)
    (hθ : (m : ℝ)*θ^2 ≤ a^2) (s : Fin m → Bool) : ‖paddedSignVector (d := d) θ s‖ ≤ a := by
  have hh := paddedSignVector_norm_sq hmd θ s
  have hn := norm_nonneg (paddedSignVector (d := d) θ s)
  nlinarith

theorem monotone_block_path_bound {d T K : ℕ} (u : Fin K → (ballDomain d).carrier)
    (b : Fin T → Fin K) (hb : Monotone b) (a : ℝ) (ha : 0 ≤ a)
    (hu : ∀ k, ‖(u k).val‖ ≤ a) : pathLength (fun t => u (b t)) ≤ 2*a*K := by
  cases T with
  | zero => simp [pathLength]; positivity
  | succ n =>
    rw [pathLength_adjacent]
    have hh : ∀ i : Fin n, ‖(u (b i.succ)).val-(u (b i.castSucc)).val‖ ≤
        2*a*((b i.succ).val-(b i.castSucc).val : ℝ) := by
      intro i
      have hmono : b i.castSucc ≤ b i.succ := hb (by simp [Fin.le_iff_val_le_val])
      by_cases he : b i.castSucc = b i.succ
      · rw [he]
        simp
      · have hgap : (b i.castSucc).val+1 ≤ (b i.succ).val := by
          have hn : (b i.castSucc).val ≠ (b i.succ).val := fun hh => he (Fin.ext hh)
          change (b i.castSucc).val ≤ (b i.succ).val at hmono
          omega
        have hgap' : (b i.castSucc).val+1 ≤ ((b i.succ).val : ℝ) := by exact_mod_cast hgap
        have hnorm := norm_sub_le (u (b i.succ)).val (u (b i.castSucc)).val
        have h1 := hu (b i.succ)
        have h2 := hu (b i.castSucc)
        nlinarith [mul_nonneg ha (show 0 ≤ ((b i.succ).val : ℝ)-(b i.castSucc).val-1 by linarith)]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hh i)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hs
    have hfirst := Fin.sum_univ_succ (fun i : Fin (n+1) => ((b i).val : ℝ))
    have hlast := Fin.sum_univ_castSucc (fun i : Fin (n+1) => ((b i).val : ℝ))
    have ht : (∑ i : Fin n, ((b i.succ).val : ℝ))-(∑ i : Fin n, ((b i.castSucc).val : ℝ)) =
        (b (Fin.last n)).val-(b 0).val := by linarith
    rw [ht] at hs
    have hk : ((b (Fin.last n)).val : ℝ) ≤ K := by exact_mod_cast (b (Fin.last n)).isLt.le
    have h0 : (0 : ℝ) ≤ (b 0).val := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left (show ((b (Fin.last n)).val : ℝ)-(b 0).val ≤ K by linarith)
      (show 0 ≤ 2*a by positivity)
    exact hs.trans hm

end Paper254
#print axioms Paper254.monotone_block_path_bound
