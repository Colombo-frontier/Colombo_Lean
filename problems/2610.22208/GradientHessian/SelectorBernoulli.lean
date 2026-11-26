import GradientHessian.SelectorProfileBounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Finite Bernoulli algebra for the actual selector weights. All sums are
finite and the endpoint probabilities zero and one are included. -/

namespace GradientHessian.SelectorBernoulli
open SelectorProfileBounds
open scoped BigOperators
noncomputable section

def bitMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p
def bitScore (p : ℝ) (b : Bool) : ℝ := ((if b then 1 else 0)-p)/varianceRoot p

theorem bitMass_nonneg {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (b : Bool) : 0 ≤ bitMass p b := by
  cases b <;> simp only [bitMass, Bool.false_eq_true, if_false, if_true] <;> linarith [hp.1, hp.2]

theorem bitMass_sum (p : ℝ) : ∑ b : Bool, bitMass p b = 1 := by simp [bitMass, Fintype.sum_bool]

theorem bitScore_mean (p : ℝ) : ∑ b : Bool, bitMass p b*bitScore p b = 0 := by
  simp only [Fintype.sum_bool, bitMass, bitScore, Bool.false_eq_true, if_false, if_true]
  ring

theorem bitScore_second {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (∑ b : Bool, bitMass p b*(bitScore p b)^2) ≤ 1 := by
  have hvar : 0 ≤ p*(1-p) := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  by_cases hv : p*(1-p) = 0
  · simp [bitMass, bitScore, varianceRoot, hv]
  · have hroot : varianceRoot p ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hvar (Ne.symm hv))).ne'
    have hs : varianceRoot p^2 = p*(1-p) := Real.sq_sqrt hvar
    have he : (∑ b : Bool, bitMass p b*(bitScore p b)^2) =
        (p*(1-p))/(varianceRoot p)^2 := by
      simp only [Fintype.sum_bool, bitMass, bitScore, Bool.false_eq_true, if_false, if_true]
      field_simp
      ring
    rw [he, hs, div_self hv]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mass (p : ι → ℝ) (ω : ι → Bool) : ℝ := ∏ i, bitMass (p i) (ω i)
def average (p : ι → ℝ) (f : (ι → Bool) → ℝ) : ℝ := ∑ ω, mass p ω*f ω

omit [DecidableEq ι] in
theorem mass_nonneg {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (ω : ι → Bool) :
    0 ≤ mass p ω := Finset.prod_nonneg (fun i _ => bitMass_nonneg (hp i) (ω i))

theorem mass_sum (p : ι → ℝ) : ∑ ω, mass p ω = 1 := by
  unfold mass
  rw [← Fintype.prod_sum]
  simp only [bitMass_sum, Finset.prod_const_one]

theorem average_one (p : ι → ℝ) : average p (fun _ => 1) = 1 := by
  simpa only [average, mul_one] using mass_sum p

theorem average_prod (p : ι → ℝ) (f : ι → Bool → ℝ) :
    average p (fun ω => ∏ i, f i (ω i)) = ∏ i, ∑ b : Bool, bitMass (p i) b*f i b := by
  unfold average mass
  simp_rw [← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]

theorem average_add (p : ι → ℝ) (f g : (ι → Bool) → ℝ) :
    average p (fun ω => f ω+g ω) = average p f+average p g := by
  simp only [average, mul_add, Finset.sum_add_distrib]

theorem average_mul_const (p : ι → ℝ) (f : (ι → Bool) → ℝ) (a : ℝ) :
    average p (fun ω => f ω*a) = average p f*a := by
  simp only [average, ← mul_assoc, Finset.sum_mul]

theorem average_const_mul (p : ι → ℝ) (a : ℝ) (f : (ι → Bool) → ℝ) :
    average p (fun ω => a*f ω) = a*average p f := by
  simp only [mul_comm a, average_mul_const]

theorem average_sum {κ : Type*} (p : ι → ℝ) (s : Finset κ)
    (f : κ → (ι → Bool) → ℝ) :
    average p (fun ω => ∑ j ∈ s, f j ω) = ∑ j ∈ s, average p (f j) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_nonneg {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    {f : (ι → Bool) → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ average p f :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (mass_nonneg hp ω) (hf ω))

theorem average_mono {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    {f g : (ι → Bool) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : average p f ≤ average p g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (mass_nonneg hp ω))

/-- Finite weighted Cauchy--Schwarz, requiring no measure-theoretic wrapper. -/
theorem average_cauchy_schwarz {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (f g : (ι → Bool) → ℝ) :
    (average p (fun ω => f ω*g ω))^2 ≤
      average p (fun ω => (f ω)^2)*average p (fun ω => (g ω)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => Real.sqrt (mass p ω)*f ω) (fun ω => Real.sqrt (mass p ω)*g ω)
  have he (ω : ι → Bool) : Real.sqrt (mass p ω)^2 = mass p ω := Real.sq_sqrt (mass_nonneg hp ω)
  have hm (ω : ι → Bool) :
      (Real.sqrt (mass p ω)*f ω)*(Real.sqrt (mass p ω)*g ω) = mass p ω*(f ω*g ω) := by
    calc
      _ = Real.sqrt (mass p ω)^2*(f ω*g ω) := by ring
      _ = _ := by rw [he]
  simpa only [hm, mul_pow, he, average] using h

def scoreMonomial (p : ι → ℝ) (s : Finset ι) (ω : ι → Bool) : ℝ :=
  ∏ i ∈ s, bitScore (p i) (ω i)

theorem scoreMonomial_full (p : ι → ℝ) (s : Finset ι) (ω : ι → Bool) :
    scoreMonomial p s ω = ∏ i, if i ∈ s then bitScore (p i) (ω i) else 1 := by
  exact (Fintype.prod_ite_mem s (fun i => bitScore (p i) (ω i))).symm

theorem scoreMonomial_gram (p : ι → ℝ) (s t : Finset ι) :
    average p (fun ω => scoreMonomial p s ω*scoreMonomial p t ω) =
      ∏ i, ∑ b : Bool, bitMass (p i) b*
        ((if i ∈ s then bitScore (p i) b else 1)*(if i ∈ t then bitScore (p i) b else 1)) := by
  simp_rw [scoreMonomial_full, ← Finset.prod_mul_distrib]
  exact average_prod p (fun i b =>
    (if i ∈ s then bitScore (p i) b else 1)*(if i ∈ t then bitScore (p i) b else 1))

/-- Products using different sets of centered independent scores are orthogonal. -/
theorem scoreMonomial_orthogonal (p : ι → ℝ) {s t : Finset ι} (hst : s ≠ t) :
    average p (fun ω => scoreMonomial p s ω*scoreMonomial p t ω) = 0 := by
  have hex : ∃ i, (i ∈ s ∧ i ∉ t) ∨ (i ∉ s ∧ i ∈ t) := by
    by_contra h
    apply hst
    ext i
    constructor
    · intro hi
      by_contra ht
      exact h ⟨i, Or.inl ⟨hi, ht⟩⟩
    · intro hi
      by_contra hs
      exact h ⟨i, Or.inr ⟨hs, hi⟩⟩
  obtain ⟨i, hi⟩ := hex
  rw [scoreMonomial_gram]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hi with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
    simp only [hs, ht, if_true, if_false, mul_one, one_mul, bitScore_mean]

theorem scoreMonomial_square {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (s : Finset ι) : average p (fun ω => (scoreMonomial p s ω)^2) ≤ 1 := by
  simp_rw [pow_two]
  rw [scoreMonomial_gram]
  apply Finset.prod_le_one
  · intro i _
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg (bitMass_nonneg (hp i) b) (mul_self_nonneg _)
  · intro i _
    by_cases hi : i ∈ s
    · simpa only [if_pos hi, ← pow_two] using bitScore_second (hp i)
    · simp only [if_neg hi, one_mul, mul_one, bitMass_sum, le_refl]

/-- Distinct square-free score monomials give a contractive orthogonal expansion. -/
theorem orthogonal_square_bound {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (s : Finset (Finset ι)) (c : Finset ι → ℝ) :
    average p (fun ω => (∑ t ∈ s, c t*scoreMonomial p t ω)^2) ≤ ∑ t ∈ s, (c t)^2 := by
  have he (ω : ι → Bool) : (∑ t ∈ s, c t*scoreMonomial p t ω)^2 =
      ∑ t ∈ s, ∑ u ∈ s, (c t*c u)*(scoreMonomial p t ω*scoreMonomial p u ω) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    ring
  simp_rw [he, average_sum, average_const_mul]
  apply Finset.sum_le_sum
  intro t ht
  have hdiag : (∑ u ∈ s, (c t*c u)*average p
      (fun ω => scoreMonomial p t ω*scoreMonomial p u ω)) =
      (c t)^2*average p (fun ω => (scoreMonomial p t ω)^2) := by
    rw [Finset.sum_eq_single t]
    · simp only [pow_two]
    · intro u _ hut
      rw [scoreMonomial_orthogonal p (Ne.symm hut), mul_zero]
    · exact fun h => False.elim (h ht)
  rw [hdiag]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (scoreMonomial_square hp t) (sq_nonneg (c t))

theorem orthogonal_absolute_bound {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (s : Finset (Finset ι)) (c : Finset ι → ℝ) :
    average p (fun ω => |∑ t ∈ s, c t*scoreMonomial p t ω|) ≤
      Real.sqrt (∑ t ∈ s, (c t)^2) := by
  have h := average_cauchy_schwarz hp
    (fun ω => |∑ t ∈ s, c t*scoreMonomial p t ω|) (fun _ => 1)
  simp only [mul_one, one_pow, average_one, sq_abs] at h
  exact Real.le_sqrt_of_sq_le (h.trans (orthogonal_square_bound hp s c))

end
end GradientHessian.SelectorBernoulli
