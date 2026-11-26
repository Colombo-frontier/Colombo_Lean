import GradientHessian.SelectorBernoulli

/-! Dimension-free finite chaos estimates for selector derivatives. The constants
depend on the derivative order, never on the number of independent registers. -/

namespace GradientHessian.SelectorChaos
open SelectorBernoulli
open scoped BigOperators
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

theorem indexed_square_bound {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (T : Finset κ) (label : κ → Finset ι) (a : κ → ℝ) (N : ℝ)
    (hcard : ∀ s ∈ T.image label, ((T.filter (fun j => label j = s)).card : ℝ) ≤ N) :
    average p (fun ω => (∑ j ∈ T, a j*scoreMonomial p (label j) ω)^2) ≤
      N*∑ j ∈ T, (a j)^2 := by
  let c : Finset ι → ℝ := fun s => ∑ j ∈ T.filter (fun j => label j = s), a j
  have he (ω : ι → Bool) : (∑ j ∈ T, a j*scoreMonomial p (label j) ω) =
      ∑ s ∈ T.image label, c s*scoreMonomial p s ω := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem label hj)
      (fun j => a j*scoreMonomial p (label j) ω)]
    apply Finset.sum_congr rfl
    intro s _
    dsimp [c]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
  simp_rw [he]
  refine (orthogonal_square_bound hp (T.image label) c).trans ?_
  calc
    ∑ s ∈ T.image label, (c s)^2 ≤
        ∑ s ∈ T.image label, N*(∑ j ∈ T.filter (fun j => label j = s), (a j)^2) := by
      apply Finset.sum_le_sum
      intro s hs
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (T.filter (fun j => label j = s))
        (fun _ => (1:ℝ)) a
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
      exact hcs.trans (mul_le_mul_of_nonneg_right (hcard s hs)
        (Finset.sum_nonneg (fun j _ => sq_nonneg (a j))))
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to
        (fun j hj => Finset.mem_image_of_mem label hj)]

theorem indexed_absolute_bound {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (T : Finset κ) (label : κ → Finset ι) (a : κ → ℝ) (N : ℝ)
    (hcard : ∀ s ∈ T.image label, ((T.filter (fun j => label j = s)).card : ℝ) ≤ N) :
    average p (fun ω => |∑ j ∈ T, a j*scoreMonomial p (label j) ω|) ≤
      Real.sqrt (N*∑ j ∈ T, (a j)^2) := by
  have h := average_cauchy_schwarz hp
    (fun ω => |∑ j ∈ T, a j*scoreMonomial p (label j) ω|) (fun _ => 1)
  simp only [mul_one, one_pow, average_one, sq_abs] at h
  exact Real.le_sqrt_of_sq_le (h.trans (indexed_square_bound hp T label a N hcard))

def tupleSet {k : ℕ} (f : Fin k → ι) : Finset ι := Finset.univ.image f

/-- At most `k^k` ordered tuples have a prescribed nonempty range of size at
most `k`. This deliberately coarse constant is sufficient through order three. -/
theorem tuple_fiber_card_le {k : ℕ} (f : Fin k → ι) :
    ((Finset.univ : Finset (Fin k → ι)).filter
      (fun g : Fin k → ι => tupleSet g = tupleSet f)).card ≤ k^k := by
  by_cases hk : k = 0
  · subst k
    simp [tupleSet]
  haveI : NeZero k := ⟨hk⟩
  let encode : (Fin k → ι) → (Fin k → Fin k) := fun g i => Function.invFun f (g i)
  have hdecode {g : Fin k → ι} (hg : tupleSet g = tupleSet f) (i : Fin k) :
      f (encode g i) = g i := by
    have hi : g i ∈ tupleSet f := hg ▸ Finset.mem_image_of_mem g (Finset.mem_univ i)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    exact Function.invFun_eq (Exists.intro j hj)
  have h := Finset.card_le_card_of_injOn encode
    (s := (Finset.univ : Finset (Fin k → ι)).filter (fun g => tupleSet g = tupleSet f))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    (by
      intro g hg h hh he
      funext i
      rw [← hdecode (Finset.mem_filter.mp hg).2 i,
        ← hdecode (Finset.mem_filter.mp hh).2 i, congrFun he i])
  simpa using h

theorem embedding_fiber_card_le {k : ℕ} (f : Fin k ↪ ι) :
    ((Finset.univ : Finset (Fin k ↪ ι)).filter
      (fun g : Fin k ↪ ι => tupleSet g = tupleSet f)).card ≤ k^k := by
  classical
  refine le_trans ?_ (tuple_fiber_card_le (f : Fin k → ι))
  apply Finset.card_le_card_of_injOn (fun g : Fin k ↪ ι => (g : Fin k → ι))
  · intro g hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hg).2⟩
  · intro g _ h _ hgh
    exact DFunLike.coe_injective hgh

theorem embedding_coefficients_square_le {k : ℕ} (a : Fin k → ι → ℝ) :
    (∑ f : Fin k ↪ ι, (∏ l, a l (f l))^2) ≤ ∏ l, ∑ i, (a l i)^2 := by
  classical
  simp_rw [← Finset.prod_pow]
  rw [Fintype.prod_sum]
  let T : Finset (Fin k → ι) := Finset.univ.image (fun f : Fin k ↪ ι => (f : Fin k → ι))
  calc
    _ = ∑ f ∈ T, ∏ l, (a l (f l))^2 := by
      rw [Finset.sum_image]
      intro f _ g _ h
      exact DFunLike.coe_injective h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun f _ _ => Finset.prod_nonneg (fun l _ => sq_nonneg (a l (f l))))

/-- The finite orthogonal-chaos estimate in the exact ordered-injection form
appearing in derivatives of the multilinear product. -/
theorem embedding_chaos_bound {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    {k : ℕ} (a : Fin k → ι → ℝ) :
    average p (fun ω => |∑ f : Fin k ↪ ι,
      (∏ l, a l (f l))*scoreMonomial p (tupleSet f) ω|) ≤
      Real.sqrt ((k:ℝ)^k*(∏ l, ∑ i, (a l i)^2)) := by
  classical
  have hcard : ∀ s ∈ (Finset.univ : Finset (Fin k ↪ ι)).image
      (fun f : Fin k ↪ ι => tupleSet f),
      (((Finset.univ : Finset (Fin k ↪ ι)).filter
        (fun f : Fin k ↪ ι => tupleSet f = s)).card : ℝ) ≤ (k:ℝ)^k := by
    intro s hs
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hs
    exact_mod_cast embedding_fiber_card_le f
  refine (indexed_absolute_bound hp Finset.univ (fun f : Fin k ↪ ι => tupleSet f)
    (fun f => ∏ l, a l (f l)) ((k:ℝ)^k) hcard).trans ?_
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (embedding_coefficients_square_le a) (by positivity))

end
end GradientHessian.SelectorChaos
