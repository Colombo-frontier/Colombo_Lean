import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Hölder control of the vector Taylor integral remainder

For a Banach-valued map, subtracting the top derivative at the expansion
point from the integral Taylor remainder leaves an integral of derivative
increments.  A Hölder operator-norm bound controls this integral without any
dimension-dependent norm conversion.
-/

open MeasureTheory
open scoped ContDiff Interval

namespace NoisyZO

noncomputable section

theorem integral_one_sub_pow (m : ℕ) (hm : 0 < m) :
    (∫ t in (0 : ℝ)..1, (1 - t) ^ (m - 1)) = 1 / (m : ℝ) := by
  calc
    (∫ t in (0 : ℝ)..1, (1 - t) ^ (m - 1)) =
        ∫ u in (0 : ℝ)..1, u ^ (m - 1) := by
          simpa using
            (intervalIntegral.integral_comp_sub_left
              (f := fun u : ℝ ↦ u ^ (m - 1)) (a := (0 : ℝ)) (b := 1) 1)
    _ = 1 / (m : ℝ) := by
      have hmcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')
      rw [integral_pow]
      rw [hmcast]
      simp

/-- The increment part of the order-`m` integral Taylor remainder. -/
def holderTaylorRemainder
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (m : ℕ) (x y : E) : F :=
  (Nat.factorial (m - 1) : ℝ)⁻¹ •
    ∫ t in (0 : ℝ)..1,
      (1 - t) ^ (m - 1) •
        ((iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x)
          (fun _ ↦ y))

/-- A dimension-free Hölder bound for the vector Taylor remainder.  The two
powers of `‖y‖` are kept separate to make the operator-norm step explicit. -/
theorem norm_holderTaylorRemainder_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (m : ℕ) (x y : E) (L α : ℝ)
    (hL : 0 ≤ L) (hα : 0 < α)
    (hholder : ∀ u v,
      ‖iteratedFDeriv ℝ m g u - iteratedFDeriv ℝ m g v‖ ≤
        L * ‖u - v‖ ^ α) :
    ‖holderTaylorRemainder g m x y‖ ≤
      (Nat.factorial (m - 1) : ℝ)⁻¹ * (L * ‖y‖ ^ α * ‖y‖ ^ m) := by
  let C : ℝ := L * ‖y‖ ^ α * ‖y‖ ^ m
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hintegrand : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(1 - t) ^ (m - 1) •
        ((iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x)
          (fun _ ↦ y))‖ ≤ C := by
    intro t ht
    have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have ht0 : 0 ≤ t := le_of_lt ht'.1
    have ht1 : t ≤ 1 := ht'.2
    have hnorm_smul : ‖t • y‖ ≤ ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (norm_nonneg y) ht1
    have hdist : ‖(x + t • y) - x‖ ≤ ‖y‖ := by
      simpa using hnorm_smul
    have hrpow : ‖(x + t • y) - x‖ ^ α ≤ ‖y‖ ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) hdist (le_of_lt hα)
    have hop :
        ‖iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x‖ ≤
          L * ‖y‖ ^ α := by
      exact (hholder (x + t • y) x).trans
        (mul_le_mul_of_nonneg_left hrpow hL)
    have heval :=
      (iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x).le_opNorm
        (fun _ ↦ y)
    have heval' :
        ‖(iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x)
          (fun _ ↦ y)‖ ≤ C := by
      calc
        ‖(iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x)
            (fun _ ↦ y)‖ ≤
            ‖iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x‖ *
              ∏ _i : Fin m, ‖y‖ := heval
        _ ≤ (L * ‖y‖ ^ α) * ∏ _i : Fin m, ‖y‖ := by gcongr
        _ = C := by simp [C]
    have hkernel0 : 0 ≤ (1 - t) ^ (m - 1) := by positivity
    have hkernel1 : (1 - t) ^ (m - 1) ≤ 1 := by
      have hbase : 1 - t ≤ 1 := by linarith
      exact pow_le_one₀ (by linarith : 0 ≤ 1 - t) hbase
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hkernel0]
    exact (mul_le_mul_of_nonneg_left heval' hkernel0).trans
      (mul_le_of_le_one_left hC hkernel1)
  have hint :
      ‖∫ t in (0 : ℝ)..1,
        (1 - t) ^ (m - 1) •
          ((iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x)
            (fun _ ↦ y))‖ ≤ C := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hintegrand
    simpa using h
  rw [holderTaylorRemainder, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((Nat.factorial (m - 1) : ℝ)⁻¹))]
  exact mul_le_mul_of_nonneg_left hint (by positivity)

/-- The sharp first-order remainder bound behind the descent lemma.  Keeping
the factor `t` in the derivative increment gives the usual constant `1/2`. -/
theorem norm_holderTaylorRemainder_one_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (x y : E) (L : ℝ) (hL : 0 ≤ L)
    (hholder : ∀ u v,
      ‖iteratedFDeriv ℝ 1 g u - iteratedFDeriv ℝ 1 g v‖ ≤
        L * ‖u - v‖) :
    ‖holderTaylorRemainder g 1 x y‖ ≤ L * ‖y‖ ^ 2 / 2 := by
  let C : ℝ := L * ‖y‖ ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpoint : ∀ᵐ t ∂volume,
      t ∈ Set.Ioc (0 : ℝ) 1 →
        ‖(iteratedFDeriv ℝ 1 g (x + t • y) - iteratedFDeriv ℝ 1 g x)
          (fun _ ↦ y)‖ ≤ C * t := by
    filter_upwards with t
    intro ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have hdist : ‖(x + t • y) - x‖ = t * ‖y‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hop :
        ‖iteratedFDeriv ℝ 1 g (x + t • y) - iteratedFDeriv ℝ 1 g x‖ ≤
          L * (t * ‖y‖) := by
      simpa only [hdist] using hholder (x + t • y) x
    have heval :=
      (iteratedFDeriv ℝ 1 g (x + t • y) - iteratedFDeriv ℝ 1 g x).le_opNorm
        (fun _ ↦ y)
    calc
      ‖(iteratedFDeriv ℝ 1 g (x + t • y) - iteratedFDeriv ℝ 1 g x)
          (fun _ ↦ y)‖ ≤
          ‖iteratedFDeriv ℝ 1 g (x + t • y) - iteratedFDeriv ℝ 1 g x‖ *
            ∏ _i : Fin 1, ‖y‖ := heval
      _ ≤ (L * (t * ‖y‖)) * ∏ _i : Fin 1, ‖y‖ := by gcongr
      _ = C * t := by simp [C]; ring
  have hpoly : IntervalIntegrable (fun t : ℝ ↦ C * t) volume 0 1 := by
    exact (by fun_prop : Continuous (fun t : ℝ ↦ C * t)).intervalIntegrable 0 1
  have hint := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun t : ℝ ↦
      (iteratedFDeriv ℝ 1 g (x + t • y) - iteratedFDeriv ℝ 1 g x)
        (fun _ ↦ y))
    (g := fun t : ℝ ↦ C * t)
    (by norm_num : (0 : ℝ) ≤ 1) hpoint hpoly
  have hpolyIntegral :
      (∫ t in (0 : ℝ)..1, C * t) = C / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
    ring
  rw [holderTaylorRemainder]
  norm_num only [Nat.factorial, Nat.cast_one, Nat.reduceSub, inv_one, pow_zero, one_smul]
  simpa only [C] using hint.trans_eq hpolyIntegral

/-- The sharp cubic remainder constant used at the endpoint `β = 4`.
For a Lipschitz second derivative, retaining both factors of `t` and
`1 - t` in the integral kernel gives `∫₀¹ (1-t)t = 1/6`. -/
theorem norm_holderTaylorRemainder_two_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (x y : E)
    (hholder : ∀ u v,
      ‖iteratedFDeriv ℝ 2 g u - iteratedFDeriv ℝ 2 g v‖ ≤ ‖u - v‖) :
    ‖holderTaylorRemainder g 2 x y‖ ≤ ‖y‖ ^ 3 / 6 := by
  let C : ℝ := ‖y‖ ^ 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint : ∀ᵐ t ∂volume,
      t ∈ Set.Ioc (0 : ℝ) 1 →
        ‖(1 - t) •
          ((iteratedFDeriv ℝ 2 g (x + t • y) - iteratedFDeriv ℝ 2 g x)
            (fun _ ↦ y))‖ ≤ C * ((1 - t) * t) := by
    filter_upwards with t
    intro ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have ht1 : t ≤ 1 := ht.2
    have hdist : ‖(x + t • y) - x‖ = t * ‖y‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hop :
        ‖iteratedFDeriv ℝ 2 g (x + t • y) - iteratedFDeriv ℝ 2 g x‖ ≤
          t * ‖y‖ := by
      simpa only [hdist] using hholder (x + t • y) x
    have heval :=
      (iteratedFDeriv ℝ 2 g (x + t • y) - iteratedFDeriv ℝ 2 g x).le_opNorm
        (fun _ ↦ y)
    have heval' :
        ‖(iteratedFDeriv ℝ 2 g (x + t • y) - iteratedFDeriv ℝ 2 g x)
          (fun _ ↦ y)‖ ≤ t * C := by
      calc
        ‖(iteratedFDeriv ℝ 2 g (x + t • y) - iteratedFDeriv ℝ 2 g x)
            (fun _ ↦ y)‖ ≤
            ‖iteratedFDeriv ℝ 2 g (x + t • y) - iteratedFDeriv ℝ 2 g x‖ *
              ∏ _i : Fin 2, ‖y‖ := heval
        _ ≤ (t * ‖y‖) * ∏ _i : Fin 2, ‖y‖ := by
          gcongr
        _ = t * C := by simp [C]; ring
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
    calc
      (1 - t) *
          ‖(iteratedFDeriv ℝ 2 g (x + t • y) - iteratedFDeriv ℝ 2 g x)
            (fun _ ↦ y)‖ ≤ (1 - t) * (t * C) := by gcongr
      _ = C * ((1 - t) * t) := by ring
  have hpoly : IntervalIntegrable (fun t : ℝ ↦ C * ((1 - t) * t)) volume 0 1 := by
    exact (by fun_prop : Continuous (fun t : ℝ ↦ C * ((1 - t) * t))).intervalIntegrable 0 1
  have hint := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun t : ℝ ↦
      (1 - t) •
        ((iteratedFDeriv ℝ 2 g (x + t • y) - iteratedFDeriv ℝ 2 g x)
          (fun _ ↦ y)))
    (g := fun t : ℝ ↦ C * ((1 - t) * t))
    (by norm_num : (0 : ℝ) ≤ 1) hpoint hpoly
  have hpolyIntegral :
      (∫ t in (0 : ℝ)..1, C * ((1 - t) * t)) = C / 6 := by
    calc
      (∫ t in (0 : ℝ)..1, C * ((1 - t) * t)) =
          C * ∫ t in (0 : ℝ)..1, (t - t ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = C / 6 := by
        rw [intervalIntegral.integral_sub]
        · rw [integral_id, integral_pow]
          norm_num
          ring
        · exact continuous_id.intervalIntegrable 0 1
        · exact (continuous_id.pow 2).intervalIntegrable 0 1
  rw [holderTaylorRemainder]
  norm_num only [Nat.factorial, Nat.cast_one, inv_one, one_smul]
  simpa only [pow_one, C] using hint.trans_eq hpolyIntegral

/-- Splitting the integral Taylor term into its top Taylor coefficient and
the Hölder increment remainder.  The only integrability premise concerns the
increment integrand; the constant top-derivative term is automatically
integrable. -/
theorem integralTaylorTerm_eq_top_add_holderRemainder
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (m : ℕ) (hm : 0 < m) (x y : E)
    (hinc : IntervalIntegrable (fun t : ℝ ↦
      (1 - t) ^ (m - 1) •
        ((iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x)
          (fun _ ↦ y))) volume 0 1) :
    (Nat.factorial (m - 1) : ℝ)⁻¹ •
        (∫ t in (0 : ℝ)..1,
          (1 - t) ^ (m - 1) •
            (iteratedFDeriv ℝ m g (x + t • y) (fun _ ↦ y))) =
      (Nat.factorial m : ℝ)⁻¹ •
          (iteratedFDeriv ℝ m g x (fun _ ↦ y)) +
        holderTaylorRemainder g m x y := by
  let top : F := iteratedFDeriv ℝ m g x (fun _ ↦ y)
  let inc : ℝ → F := fun t ↦
    (1 - t) ^ (m - 1) •
      ((iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x)
        (fun _ ↦ y))
  let base : ℝ → F := fun t ↦ (1 - t) ^ (m - 1) • top
  have hbase : IntervalIntegrable base volume 0 1 := by
    have hcont : Continuous base := by
      dsimp [base]
      fun_prop
    exact hcont.intervalIntegrable (μ := volume) 0 1
  have hsplit :
      (∫ t in (0 : ℝ)..1,
        (1 - t) ^ (m - 1) •
          (iteratedFDeriv ℝ m g (x + t • y) (fun _ ↦ y))) =
        (∫ t in (0 : ℝ)..1, inc t) + ∫ t in (0 : ℝ)..1, base t := by
    calc
      (∫ t in (0 : ℝ)..1,
        (1 - t) ^ (m - 1) •
          (iteratedFDeriv ℝ m g (x + t • y) (fun _ ↦ y))) =
          ∫ t in (0 : ℝ)..1, inc t + base t := by
            apply intervalIntegral.integral_congr
            intro t _
            dsimp [inc, base, top]
            simp only [sub_apply]
            module
      _ = (∫ t in (0 : ℝ)..1, inc t) + ∫ t in (0 : ℝ)..1, base t := by
        rw [intervalIntegral.integral_add]
        · simpa only [inc] using hinc
        · exact hbase
  have hbaseIntegral :
      (∫ t in (0 : ℝ)..1, base t) = (1 / (m : ℝ)) • top := by
    dsimp [base]
    rw [intervalIntegral.integral_smul_const, integral_one_sub_pow m hm]
  have hfac :
      (Nat.factorial (m - 1) : ℝ)⁻¹ * (1 / (m : ℝ)) =
        (Nat.factorial m : ℝ)⁻¹ := by
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hfacR :
        (m : ℝ) * (Nat.factorial (m - 1) : ℝ) =
          (Nat.factorial m : ℝ) := by
      exact_mod_cast Nat.mul_factorial_pred hm.ne'
    rw [← hfacR]
    field_simp
  rw [hsplit, hbaseIntegral, smul_add, smul_smul, hfac]
  simpa only [top, inc, holderTaylorRemainder] using
    (add_comm
      ((Nat.factorial (m - 1) : ℝ)⁻¹ • (∫ t in (0 : ℝ)..1, inc t))
      ((Nat.factorial m : ℝ)⁻¹ • top))

theorem holderTaylorRemainder_intervalIntegrable
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (m : ℕ) (x y : E)
    (hsmooth : ∀ (t : ℝ) (_ht : t ∈ Set.Icc 0 1),
      ContDiffAt ℝ m g (x + t • y)) :
    IntervalIntegrable (fun t : ℝ ↦
      (1 - t) ^ (m - 1) •
        ((iteratedFDeriv ℝ m g (x + t • y) - iteratedFDeriv ℝ m g x)
          (fun _ ↦ y))) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  intro t ht
  have haffine : ContinuousWithinAt (fun s : ℝ ↦ x + s • y)
      (Set.Icc 0 1) t := by fun_prop
  have houter : ContinuousAt (iteratedFDeriv ℝ m g) (x + t • y) :=
    (hsmooth t ht).continuousAt_iteratedFDeriv (by rfl)
  have hderiv : ContinuousWithinAt
      (fun s : ℝ ↦ iteratedFDeriv ℝ m g (x + s • y)) (Set.Icc 0 1) t :=
    by
      change ContinuousWithinAt
        (iteratedFDeriv ℝ m g ∘ fun s : ℝ ↦ x + s • y) (Set.Icc 0 1) t
      exact ContinuousAt.comp_continuousWithinAt
        (f := fun s : ℝ ↦ x + s • y) houter haffine
  let eval :
      ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F →L[ℝ] F :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin m ↦ E) F (fun _ ↦ y)
  have heval : ContinuousWithinAt
      (fun s : ℝ ↦
        (iteratedFDeriv ℝ m g (x + s • y) - iteratedFDeriv ℝ m g x)
          (fun _ ↦ y)) (Set.Icc 0 1) t := by
    exact eval.continuous.continuousAt.comp_continuousWithinAt
      (hderiv.sub continuousWithinAt_const)
  exact (by fun_prop : ContinuousWithinAt
      (fun s : ℝ ↦ (1 - s) ^ (m - 1)) (Set.Icc 0 1) t).smul heval

/-- Vector Taylor expansion through order `m`, with the highest-order
derivative frozen at the base point and the remaining increment isolated as
`holderTaylorRemainder`. -/
theorem vector_taylor_eq_sum_add_holderRemainder
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (m : ℕ) (hm : 0 < m) (x y : E)
    (hsmooth : ∀ (t : ℝ) (_ht : t ∈ Set.Icc 0 1),
      ContDiffAt ℝ m g (x + t • y)) :
    g (x + y) =
      (∑ k ∈ Finset.range m,
        (Nat.factorial k : ℝ)⁻¹ • (iteratedFDeriv ℝ k g x (fun _ ↦ y))) +
      (Nat.factorial m : ℝ)⁻¹ •
        (iteratedFDeriv ℝ m g x (fun _ ↦ y)) +
      holderTaylorRemainder g m x y := by
  have hmPred : m - 1 + 1 = m := Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr hm.ne')
  have hsmooth' : ∀ (t : ℝ) (ht : t ∈ Set.Icc 0 1),
      ContDiffAt ℝ (↑(m - 1 + 1) : ℕ∞ω) g (x + t • y) := by
    intro t ht
    simpa only [hmPred] using hsmooth t ht
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := g) (x := x) (y := y) (n := m - 1) hsmooth'
  have hinc := holderTaylorRemainder_intervalIntegrable g m x y hsmooth
  have hsplit := integralTaylorTerm_eq_top_add_holderRemainder
    g m hm x y hinc
  rw [hmPred] at hTaylor
  calc
    g (x + y) =
        (∑ k ∈ Finset.range m,
          (Nat.factorial k : ℝ)⁻¹ • (iteratedFDeriv ℝ k g x (fun _ ↦ y))) +
        (Nat.factorial (m - 1) : ℝ)⁻¹ •
          (∫ t in (0 : ℝ)..1,
            (1 - t) ^ (m - 1) •
              (iteratedFDeriv ℝ m g (x + t • y) (fun _ ↦ y))) := hTaylor
    _ = (∑ k ∈ Finset.range m,
          (Nat.factorial k : ℝ)⁻¹ • (iteratedFDeriv ℝ k g x (fun _ ↦ y))) +
        ((Nat.factorial m : ℝ)⁻¹ •
          (iteratedFDeriv ℝ m g x (fun _ ↦ y)) +
          holderTaylorRemainder g m x y) := by rw [hsplit]
    _ = (∑ k ∈ Finset.range m,
          (Nat.factorial k : ℝ)⁻¹ • (iteratedFDeriv ℝ k g x (fun _ ↦ y))) +
        (Nat.factorial m : ℝ)⁻¹ •
          (iteratedFDeriv ℝ m g x (fun _ ↦ y)) +
        holderTaylorRemainder g m x y := by abel

end

end NoisyZO
