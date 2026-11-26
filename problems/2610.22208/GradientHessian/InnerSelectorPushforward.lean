import GradientHessian.InnerSelector
import GradientHessian.SelectorBernoulli
import GradientHessian.InnerDerivativeTools

/-! The finite Bernoulli first-zero pushforward is exactly the source
stick-breaking sum. This is pure algebra, valid even for arbitrary real ports. -/

noncomputable section
namespace GradientHessian.InnerSelectorPushforward

open SelectorBernoulli

def stopPayoff : (m : ℕ) → (Fin m → ℝ) → ℝ → (Fin m → Bool) → ℝ
  | 0, _, terminal, _ => terminal
  | m + 1, e, terminal, ω => if ω 0 then
      stopPayoff m (fun i => e i.succ) terminal (fun i => ω i.succ) else e 0

def boolSplit (m : ℕ) : (Fin (m + 1) → Bool) ≃ Bool × (Fin m → Bool) where
  toFun ω := (ω 0, fun i => ω i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv ω := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by rfl

theorem mass_cons (m : ℕ) (p : Fin (m + 1) → ℝ) (b : Bool) (ω : Fin m → Bool) :
    mass p (Fin.cons b ω) = bitMass (p 0) b * mass (fun i => p i.succ) ω := by
  simp [mass, Fin.prod_univ_succ]

theorem sum_mass_succ (m : ℕ) (p : Fin (m + 1) → ℝ) (f : (Fin (m + 1) → Bool) → ℝ) :
    (∑ ω, mass p ω * f ω) =
      (1 - p 0) * (∑ ω : Fin m → Bool, mass (fun i => p i.succ) ω * f (Fin.cons false ω)) +
      p 0 * (∑ ω : Fin m → Bool, mass (fun i => p i.succ) ω * f (Fin.cons true ω)) := by
  rw [← (boolSplit m).symm.sum_comp (fun ω => mass p ω * f ω), Fintype.sum_prod_type]
  simp only [boolSplit, Equiv.coe_fn_symm_mk, Fintype.sum_bool, mass_cons, bitMass,
    Bool.false_eq_true, if_false, if_true]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem stopPayoff_abs_bound (m : ℕ) (e : Fin m → ℝ) (terminal : ℝ) {B : ℝ}
    (he : ∀ i, |e i| ≤ B) (ht : |terminal| ≤ B) (ω : Fin m → Bool) :
    |stopPayoff m e terminal ω| ≤ B := by
  induction m with
  | zero => exact ht
  | succ m ih =>
    unfold stopPayoff
    split_ifs
    · exact ih _ (fun i => he i.succ) (fun i => ω i.succ)
    · exact he 0

/-- Exact first-zero pushforward, including the all-one terminal payoff. -/
theorem bernoulli_pushforward (m : ℕ) (p e : Fin m → ℝ) (terminal : ℝ) :
    (∑ ω, mass p ω * stopPayoff m e terminal ω) =
      InnerSelector.select m p e + (∏ i, p i) * terminal := by
  induction m with
  | zero => simp [mass, stopPayoff, InnerSelector.select]
  | succ m ih =>
    rw [sum_mass_succ]
    simp only [stopPayoff, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, if_false, if_true]
    rw [← Finset.sum_mul, mass_sum, one_mul, ih, InnerSelector.select, Fin.prod_univ_succ]
    ring

theorem bernoulli_pushforward_zero (m : ℕ) (p e : Fin m → ℝ) :
    (∑ ω, mass p ω * stopPayoff m e 0 ω) = InnerSelector.select m p e := by
  simpa using bernoulli_pushforward m p e 0

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The first-zero coordinate is fixed by the bit string, independently of
the point at which payloads and their derivatives are evaluated. -/
theorem stopPayoff_function_eq (m : ℕ) (ω : Fin m → Bool) (e : Fin m → F → ℝ) (terminal : F → ℝ) :
    (fun x => stopPayoff m (fun i => e i x) (terminal x) ω) = terminal ∨
      ∃ i, (fun x => stopPayoff m (fun i => e i x) (terminal x) ω) = e i := by
  induction m with
  | zero => exact Or.inl rfl
  | succ m ih =>
    by_cases hω : ω 0 = true
    · have heq : (fun x => stopPayoff (m + 1) (fun i => e i x) (terminal x) ω) =
          (fun x => stopPayoff m (fun i => e i.succ x) (terminal x) (fun i => ω i.succ)) := by
        funext x
        simp [stopPayoff, hω]
      rw [heq]
      rcases ih (fun i => ω i.succ) (fun i => e i.succ) with h | ⟨i, hi⟩
      · exact Or.inl h
      · exact Or.inr ⟨i.succ, hi⟩
    · right
      refine ⟨0, ?_⟩
      funext x
      simp [stopPayoff, hω]

theorem stopPayoff_contDiff (m : ℕ) (ω : Fin m → Bool) (e : Fin m → F → ℝ)
    (terminal : F → ℝ) {N : WithTop ℕ∞} (he : ∀ i, ContDiff ℝ N (e i))
    (ht : ContDiff ℝ N terminal) :
    ContDiff ℝ N (fun x => stopPayoff m (fun i => e i x) (terminal x) ω) := by
  rcases stopPayoff_function_eq m ω e terminal with h | ⟨i, h⟩
  · rwa [h]
  · rw [h]
    exact he i

theorem stopPayoff_derivative_bound (m : ℕ) (ω : Fin m → Bool) (e : Fin m → F → ℝ)
    (terminal : F → ℝ) (x : F) (n : ℕ) {B : ℝ}
    (he : ∀ i, ‖iteratedFDeriv ℝ n (e i) x‖ ≤ B)
    (ht : ‖iteratedFDeriv ℝ n terminal x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => stopPayoff m (fun i => e i y) (terminal y) ω) x‖ ≤ B := by
  rcases stopPayoff_function_eq m ω e terminal with h | ⟨i, h⟩
  · rwa [h]
  · rw [h]
    exact he i

end GradientHessian.InnerSelectorPushforward
