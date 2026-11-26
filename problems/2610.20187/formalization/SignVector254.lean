import HiddenSigns254
import Problem254

noncomputable section
open scoped BigOperators
namespace Paper254

def signVector {d : ℕ} (θ : ℝ) (s : Fin d → Bool) : Space d :=
  WithLp.toLp 2 (fun j => signedMean θ (s j))

theorem signVector_norm_sq {d : ℕ} (θ : ℝ) (s : Fin d → Bool) :
    ‖signVector θ s‖^2 = (d : ℝ)*θ^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ j : Fin d, ‖signedMean θ (s j)‖^2) = _
  simp [Real.norm_eq_abs, sq_abs, signedMean_sq]

def signVectorInBall {d : ℕ} (θ : ℝ) (hθ : (d : ℝ)*θ^2 ≤ 1/4)
    (s : Fin d → Bool) : (ballDomain d).carrier :=
  ⟨signVector θ s, by
    change signVector θ s ∈ Metric.closedBall 0 (1/2)
    rw [Metric.mem_closedBall, dist_zero_right]
    have hh := signVector_norm_sq θ s
    have hn := norm_nonneg (signVector θ s)
    nlinarith⟩

theorem prefix_mod_count (m n t : ℕ) (hm : 0 < m) (ht : t ≤ n*m) (j : ℕ) :
    ((Finset.univ : Finset (Fin t)).filter (fun i => i.val%m = j)).card ≤ n := by
  let src := (Finset.univ : Finset (Fin t)).filter (fun i => i.val%m = j)
  let f := fun i : Fin t => i.val/m
  have hmap : Set.MapsTo f src (Finset.range n) := by
    intro i _
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hm).mpr
    exact lt_of_lt_of_le i.isLt ht
  have hinj : Set.InjOn f src := by
    intro i hi k hk he
    have hi' := (Finset.mem_filter.mp hi).2
    have hk' := (Finset.mem_filter.mp hk).2
    have hdi := Nat.mod_add_div i.val m
    have hdk := Nat.mod_add_div k.val m
    apply Fin.ext
    change i.val/m = k.val/m at he
    rw [he] at hdi
    omega
  have hh := Finset.card_le_card_of_injOn f hmap hinj
  simpa only [Finset.card_range] using hh

theorem prefix_mod_information (m n t : ℕ) (hm : 0 < m) (ht : t ≤ n*m)
    (j : ℕ) (θ : ℝ) :
    (∑ i : Fin t, if i.val%m = j then θ^2 else 0) ≤ (n : ℝ)*θ^2 := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : ((((Finset.univ : Finset (Fin t)).filter (fun i => i.val%m = j)).card : ℝ)) ≤ n := by
    exact_mod_cast prefix_mod_count m n t hm ht j
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg θ)

end Paper254
#print axioms Paper254.signVector_norm_sq
#print axioms Paper254.prefix_mod_information
