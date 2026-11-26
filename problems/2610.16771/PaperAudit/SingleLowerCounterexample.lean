import Mathlib

namespace PaperAudit.SingleLowerCounterexample



namespace OriginalAudit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem smooth_descent_upper
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x s : E) :
    f (x + s) ≤ f x + inner ℝ (gradient f x) s + L / 2 * ‖s‖ ^ 2 := by
  let a : ℝ → E := fun t => x + t • s
  let p : ℝ → ℝ := fun t =>
    f (a t) - f x - t * inner ℝ (gradient f x) s - L / 2 * t ^ 2 * ‖s‖ ^ 2
  let p' : ℝ → ℝ := fun t =>
    inner ℝ (gradient f (a t)) s - inner ℝ (gradient f x) s -
      L / 2 * (2 * t) * ‖s‖ ^ 2
  have ha : ∀ t : ℝ, HasDerivAt a s t := by
    intro t
    simpa only [a, one_smul, id_eq] using
      (((hasDerivAt_id t).smul_const s).const_add x)
  have hp : ∀ t : ℝ, HasDerivAt p (p' t) t := by
    intro t
    have hf : HasDerivAt (fun t => f (a t)) (inner ℝ (gradient f (a t)) s) t := by
      simpa only [Function.comp_def, inner_gradient_left] using
        ((hdiff (a t)).hasFDerivAt.comp_hasDerivAt t (ha t))
    have hlin : HasDerivAt (fun t : ℝ => t * inner ℝ (gradient f x) s)
        (inner ℝ (gradient f x) s) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (gradient f x) s)
    have hquad : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖s‖ ^ 2)
        (L / 2 * (2 * t) * ‖s‖ ^ 2) t := by
      have ht := (((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖s‖ ^ 2)
      convert ht using 1 <;> first | rfl | simp
    simpa only [p, p', Pi.sub_def] using ((hf.sub_const (f x)).sub hlin).sub hquad
  have hpnonpos : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), p' t ≤ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hl := hlip (a t) x
    have hnorm : ‖a t - x‖ = t * ‖s‖ := by
      simp [a, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [hnorm] at hl
    have hi := real_inner_le_norm (gradient f (a t) - gradient f x) s
    rw [inner_sub_left] at hi
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg s)
    dsimp [p']
    nlinarith only [hi, hm]
  have hm : AntitoneOn p (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t _ => (hp t).continuousAt.continuousWithinAt)
      (fun t _ => (hp t).hasDerivWithinAt) hpnonpos
  have h := hm (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
  have h' := h
  dsimp [p, a] at h'
  simp only [one_smul, zero_smul, add_zero, zero_mul, one_pow, zero_pow (by omega : 2 ≠ 0)] at h'
  linarith

theorem gradient_step_descent
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x : E) :
    f (x - L⁻¹ • gradient f x) ≤ f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
  have h := smooth_descent_upper f L hL hdiff hlip x (- (L⁻¹ • gradient f x))
  rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at h
  have hn : L ≠ 0 := ne_of_gt hL
  have heq : f x - L⁻¹ * ‖gradient f x‖ ^ 2 +
      L / 2 * (L⁻¹ * ‖gradient f x‖) ^ 2 =
      f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
    field_simp
    <;> ring
  have h' : f (x - L⁻¹ • gradient f x) ≤
      f x - L⁻¹ * ‖gradient f x‖ ^ 2 +
        L / 2 * (L⁻¹ * ‖gradient f x‖) ^ 2 := by
    simpa only [sub_eq_add_neg] using h
  rwa [heq] at h'


theorem exists_small_gradient
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hbelow : ∃ b : ℝ, ∀ x : E, b ≤ f x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ x : E, ‖gradient f x‖ ≤ δ := by
  by_contra hgoal
  have hlarge : ∀ x : E, δ < ‖gradient f x‖ := by
    intro x
    exact lt_of_not_ge (fun hx => hgoal ⟨x, hx⟩)
  obtain ⟨b, hb⟩ := hbelow
  let c : ℝ := δ ^ 2 / (2 * L)
  have hc : 0 < c := by dsimp [c]; positivity
  let x : ℕ → E := fun n =>
    Nat.rec (0 : E) (fun _ z => z - L⁻¹ • gradient f z) n
  have hx (n : ℕ) : x (n + 1) = x n - L⁻¹ • gradient f (x n) := by rfl
  have hstep (n : ℕ) : f (x (n + 1)) ≤ f (x n) - c := by
    have hsq : δ ^ 2 ≤ ‖gradient f (x n)‖ ^ 2 :=
      (sq_le_sq₀ hδ.le (norm_nonneg _)).2 (hlarge (x n)).le
    have hquot : c ≤ ‖gradient f (x n)‖ ^ 2 / (2 * L) := by
      dsimp [c]
      exact div_le_div_of_nonneg_right hsq (by positivity)
    rw [hx n]
    exact le_trans (gradient_step_descent f L hL hdiff hlip (x n))
      (sub_le_sub_left hquot (f (x n)))
  have hvalues : ∀ n : ℕ, f (x n) ≤ f (x 0) - (n : ℝ) * c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hstep n
      have hncast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
      rw [hncast]
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((f (x 0) - b) / c)
  have hnprod : f (x 0) - b < (n : ℝ) * c := (div_lt_iff₀ hc).mp hn
  have hv := hvalues n
  have hb' := hb (x n)
  linarith


theorem not_uniform_positive_gradient_lower_bound
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hbelow : ∃ b : ℝ, ∀ x : E, b ≤ f x)
    (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ x : E, δ ≤ ‖gradient f x‖ := by
  intro hlarge
  obtain ⟨x, hx⟩ := exists_small_gradient f L hL hdiff hlip hbelow (δ / 2) (by positivity)
  have hh := hlarge x
  linarith


theorem lipschitz_gradient_of_bounded_fderiv_gradient
    (f : E → ℝ) (L : ℝ)
    (hgrad_diff : Differentiable ℝ (gradient f))
    (hbound : ∀ x : E, ‖fderiv ℝ (gradient f) x‖ ≤ L) :
    ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := by
  intro x y
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (Set.univ : Set E)) => hgrad_diff z)
    (fun z (_ : z ∈ (Set.univ : Set E)) => hbound z)
    (convex_univ : Convex ℝ (Set.univ : Set E))
    (Set.mem_univ y) (Set.mem_univ x)


theorem exists_small_gradient_of_bounded_fderiv_gradient
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hgrad_diff : Differentiable ℝ (gradient f))
    (hbound : ∀ x : E, ‖fderiv ℝ (gradient f) x‖ ≤ L)
    (hbelow : ∃ b : ℝ, ∀ x : E, b ≤ f x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ x : E, ‖gradient f x‖ ≤ δ := by
  exact exists_small_gradient f L hL hdiff
    (lipschitz_gradient_of_bounded_fderiv_gradient f L hgrad_diff hbound) hbelow δ hδ

end OriginalAudit


open MeasureTheory
open scoped ContDiff Topology

namespace OriginalGloballyCorrectStationaryVerifier
noncomputable section
set_option maxHeartbeats 5000000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev AllJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (j : ℕ) → E [×j]→L[ℝ] ℝ

def oracle (f : E → ℝ) (x : E) : AllJet E := fun j => iteratedFDeriv ℝ j f x

def decodeGradient (a : AllJet E) : E :=
  (InnerProductSpace.toDual ℝ E).symm ((continuousMultilinearCurryFin1 ℝ E ℝ) (a 1))

theorem decode_actual_oracle (f : E → ℝ) (x : E) :
    decodeGradient (oracle f x) = gradient f x := by
  unfold decodeGradient gradient
  congr 1
  ext v
  simp [oracle,continuousMultilinearCurryFin1_apply]

/-- Status zero is the initial verification query, status one is a fallback GD
query, and status two is a terminal output. The state stores no function. -/
abbrev State (E : Type*) := ℕ × E

def query (s : State E) : E := s.2
def stopped (s : State E) : Prop := s.1 = 2
def output (s : State E) : E := s.2

def update (L delta : ℝ) (s : State E) (a : AllJet E) : State E :=
  if ‖decodeGradient a‖ ≤ delta then (2,s.2)
  else if s.1 = 0 then (1,0)
  else (1,s.2 - L⁻¹ • decodeGradient a)

/-- A literal finite oracle machine: each nonterminal iteration requests the
whole infinite derivative bundle once and increments the charged count once. -/
def run (L delta : ℝ) (get : E → AllJet E) : ℕ → State E → State E × ℕ
  | 0, s => (s,0)
  | n+1, s => if stopped s then (s,0) else
      let r := run L delta get n (update L delta s (get (query s)))
      (r.1,r.2+1)

theorem run_stopped (L delta : ℝ) (get : E → AllJet E) (n : ℕ) (x : E) :
    run L delta get n (2,x) = ((2,x),0) := by
  cases n <;> simp [run,stopped]

theorem actual_calls_le_fuel (L delta : ℝ) (get : E → AllJet E) (n : ℕ) (s : State E) :
    (run L delta get n s).2 ≤ n := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    by_cases hs : stopped s
    · simp [run,hs]
    · simp only [run,if_neg hs]
      have h := ih (update L delta s (get (query s)))
      omega

/-- This bound concerns the actual executed path, not a padding budget. -/
theorem selected_function_exactly_one_call
    (L delta : ℝ) (f : E → ℝ) (w : E) (h : ‖gradient f w‖ ≤ delta) (n : ℕ) :
    run L delta (oracle f) (n+1) (0,w) = ((2,w),1) := by
  simp only [run,stopped,show (0:ℕ) ≠ 2 by omega,if_false,query,update,
    decode_actual_oracle,if_pos h,run_stopped,Nat.zero_add]

def fallbackFuel (L delta Delta : ℝ) : ℕ := ⌈4*Delta*L/delta^2⌉₊ + 1
def totalFuel (L delta Delta : ℝ) : ℕ := fallbackFuel L delta Delta + 1

theorem fallback_fuel_decrease (L delta Delta : ℝ) (hL : 0 < L) (hd : 0 < delta)
    (hD : 0 ≤ Delta) :
    Delta < (fallbackFuel L delta Delta : ℝ) * (delta^2/(2*L)) := by
  have hc : 0 < delta^2/(2*L) := by positivity
  have hn : 4*Delta*L/delta^2 ≤ (⌈4*Delta*L/delta^2⌉₊ : ℝ) := Nat.le_ceil _
  have hDscaled : Delta/(delta^2/(2*L)) ≤ 4*Delta*L/delta^2 := by
    field_simp
    nlinarith [sq_pos_of_pos hd]
  have hlt : Delta/(delta^2/(2*L)) < (fallbackFuel L delta Delta : ℝ) := by
    unfold fallbackFuel
    push_cast
    linarith
  exact (div_lt_iff₀ hc).mp hlt

/-- Exact fallback dynamics either has already certified the true gradient, or
has spent one genuine descent step per charged fallback query. -/
theorem fallback_success_or_decrease
    (f : E → ℝ) (L delta : ℝ) (hL : 0 < L) (hd : 0 < delta)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L*‖x-y‖)
    (n : ℕ) (x : E) :
    let r := run L delta (oracle f) n (1,x)
    (r.1.1 = 2 ∧ ‖gradient f r.1.2‖ ≤ delta) ∨
      (r.1.1 = 1 ∧ f r.1.2 ≤ f x - (n:ℝ)*(delta^2/(2*L))) := by
  induction n generalizing x with
  | zero => right; simp [run]
  | succ n ih =>
    by_cases hg : ‖gradient f x‖ ≤ delta
    · left
      simpa [run,stopped,query,update,decode_actual_oracle,hg,run_stopped] using hg
    · have hs : f (x - L⁻¹ • gradient f x) ≤ f x - delta^2/(2*L) := by
        have hsq : delta^2 ≤ ‖gradient f x‖^2 :=
          (sq_le_sq₀ hd.le (norm_nonneg _)).mpr (le_of_lt (lt_of_not_ge hg))
        have hdiv := div_le_div_of_nonneg_right hsq (show 0 ≤ 2*L by positivity)
        have hdesc := OriginalAudit.gradient_step_descent f L hL hdiff hlip x
        linarith
      have hh := ih (x - L⁻¹ • gradient f x)
      simp only [run,stopped,show (1:ℕ) ≠ 2 by omega,if_false,query,update,
        decode_actual_oracle,if_neg hg,show (1:ℕ) ≠ 0 by omega] at *
      rcases hh with hh | hh
      · exact Or.inl hh
      · right
        refine ⟨hh.1,?_⟩
        have hv := hh.2
        push_cast
        linarith

/-- Correct on every smooth function in the class, independently of the chosen
code constant w. The lower bound and initial gap apply at zero, never at w. -/
theorem globally_correct_with_uniform_finite_budget
    (f : E → ℝ) (L delta Delta b : ℝ) (hL : 0 < L) (hd : 0 < delta) (hD : 0 ≤ Delta)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L*‖x-y‖)
    (hbelow : ∀ x : E, b ≤ f x) (hgap : f 0 - b ≤ Delta) (w : E) :
    let r := run L delta (oracle f) (totalFuel L delta Delta) (0,w)
    r.1.1 = 2 ∧ ‖gradient f r.1.2‖ ≤ delta ∧ r.2 ≤ ⌈4*Delta*L/delta^2⌉₊+2 := by
  have hN := fallback_fuel_decrease L delta Delta hL hd hD
  have hFallback := fallback_success_or_decrease f L delta hL hd hdiff hlip
    (fallbackFuel L delta Delta) (0:E)
  have hgood :
      (run L delta (oracle f) (fallbackFuel L delta Delta) (1,0)).1.1 = 2 ∧
      ‖gradient f (run L delta (oracle f) (fallbackFuel L delta Delta) (1,0)).1.2‖ ≤ delta := by
    rcases hFallback with hh | hh
    · exact hh
    · have hb := hbelow (run L delta (oracle f) (fallbackFuel L delta Delta) (1,0)).1.2
      have hval := hh.2
      linarith
  have hcount := actual_calls_le_fuel L delta (oracle f) (totalFuel L delta Delta) (0,w)
  have hBudget : totalFuel L delta Delta = ⌈4*Delta*L/delta^2⌉₊+2 := by
    unfold totalFuel fallbackFuel
    omega
  rw [hBudget] at hcount
  have hfinal :
      (run L delta (oracle f) (totalFuel L delta Delta) (0,w)).1.1 = 2 ∧
      ‖gradient f (run L delta (oracle f) (totalFuel L delta Delta) (0,w)).1.2‖ ≤ delta := by
    by_cases hg : ‖gradient f w‖ ≤ delta
    · rw [totalFuel,selected_function_exactly_one_call L delta f w hg]
      exact ⟨rfl,hg⟩
    · simpa [totalFuel,run,stopped,query,update,decode_actual_oracle,hg] using hgood
  exact ⟨hfinal.1,hfinal.2,hcount⟩

section BorelMachine
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace (AllJet E)] [BorelSpace (AllJet E)]

theorem decodeGradient_continuous : Continuous (decodeGradient : AllJet E → E) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    ((continuousMultilinearCurryFin1 ℝ E ℝ).continuous.comp (continuous_apply 1))

theorem all_jet_oracle_measurable (f : E → ℝ) (hf : ContDiff ℝ ∞ f) :
    Measurable (oracle f) :=
  (continuous_pi (fun j => hf.continuous_iteratedFDeriv (by exact WithTop.coe_le_coe.mpr le_top))).measurable

/-- All four operational maps are explicitly Borel. No arbitrary transcript
continuation or function-dependent callback is admitted without these proofs. -/
structure Machine where
  ask : State E → E
  stop : State E → Prop
  value : State E → E
  next : State E × AllJet E → State E
  ask_measurable : Measurable ask
  stop_measurable : MeasurableSet {s | stop s}
  value_measurable : Measurable value
  next_measurable : Measurable next

def machineRun (A : Machine (E := E)) (get : E → AllJet E) : ℕ → State E → State E × ℕ
  | 0, s => (s,0)
  | n+1, s => if A.stop s then (s,0) else
      let r := machineRun A get n (A.next (s,get (A.ask s)))
      (r.1,r.2+1)

def checkedMachine (L delta : ℝ) : Machine (E := E) where
  ask := query
  stop := stopped
  value := output
  next := fun p => update L delta p.1 p.2
  ask_measurable := measurable_snd
  stop_measurable := by
    exact measurableSet_eq_fun measurable_fst measurable_const
  value_measurable := measurable_snd
  next_measurable := by
    have hg : Measurable (fun p : State E × AllJet E => decodeGradient p.2) :=
      decodeGradient_continuous.measurable.comp measurable_snd
    have hgood : MeasurableSet {p : State E × AllJet E | ‖decodeGradient p.2‖ ≤ delta} :=
      measurableSet_le hg.norm measurable_const
    have hfirst : MeasurableSet {p : State E × AllJet E | p.1.1 = 0} :=
      measurableSet_eq_fun measurable_fst.fst measurable_const
    have hc : Measurable (fun p : State E × AllJet E => ((2:ℕ),p.1.2)) :=
      measurable_const.prodMk measurable_fst.snd
    have hr : Measurable (fun _ : State E × AllJet E => ((1:ℕ),(0:E))) := measurable_const
    have hu : Measurable (fun p : State E × AllJet E =>
        ((1:ℕ),p.1.2 - L⁻¹ • decodeGradient p.2)) :=
      measurable_const.prodMk (measurable_fst.snd.sub (measurable_const.smul hg))
    exact Measurable.ite hgood hc (Measurable.ite hfirst hr hu)

theorem checked_machine_is_actual_run (L delta : ℝ) (get : E → AllJet E) (n : ℕ) (s : State E) :
    machineRun (checkedMachine L delta) get n s = run L delta get n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [machineRun,run]
    change (if stopped s then (s,0) else
      ((machineRun (checkedMachine L delta) get n (update L delta s (get (query s)))).1,
       (machineRun (checkedMachine L delta) get n (update L delta s (get (query s)))).2+1)) = _
    rw [ih]


theorem machine_execution_measurable (A : Machine (E := E)) (get : E → AllJet E)
    (hget : Measurable get) (n : ℕ) : Measurable (machineRun A get n) := by
  induction n with
  | zero => exact measurable_id.prodMk measurable_const
  | succ n ih =>
    have hn : Measurable (fun s => A.next (s,get (A.ask s))) :=
      A.next_measurable.comp (measurable_id.prodMk (hget.comp A.ask_measurable))
    have hh := ih.comp hn
    have hstop : Measurable (fun s : State E => (s,(0:ℕ))) :=
      measurable_id.prodMk measurable_const
    have hgo : Measurable (fun s =>
        ((machineRun A get n (A.next (s,get (A.ask s)))).1,
         (machineRun A get n (A.next (s,get (A.ask s)))).2+1)) :=
      hh.fst.prodMk (hh.snd.add measurable_const)
    exact Measurable.ite A.stop_measurable hstop hgo

end BorelMachine

/-- The original smooth bounded-below class, with true Hessian norm, Hessian
Lipschitz bound and the original gap at zero. -/
structure Legal (L rho Delta : ℝ) (f : E → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  bounded_below : BddBelow (Set.range f)
  gap : f 0 - sInf (Set.range f) ≤ Delta
  hessian_norm : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ L
  hessian_lipschitz : ∀ x y,
    ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ rho*‖x-y‖

theorem Legal.gradient_differentiable {L rho Delta : ℝ} {f : E → ℝ}
    (hf : Legal L rho Delta f) : Differentiable ℝ (gradient f) := by
  have hC2 : ContDiff ℝ 2 f := hf.smooth.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hC2.fderiv_right (by norm_num)
  change Differentiable ℝ (fun z => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z))
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.differentiable.comp
    (hd.differentiable (by norm_num))

theorem Legal.gradient_lipschitz {L rho Delta : ℝ} {f : E → ℝ}
    (hf : Legal L rho Delta f) :
    ∀ x y : E, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖ :=
  OriginalAudit.lipschitz_gradient_of_bounded_fderiv_gradient f L
    hf.gradient_differentiable hf.hessian_norm

theorem Legal.lower_bound {L rho Delta : ℝ} {f : E → ℝ}
    (hf : Legal L rho Delta f) (x : E) : sInf (Set.range f) ≤ f x :=
  csInf_le hf.bounded_below (Set.mem_range_self x)

theorem uniform_global_correctness_on_original_class
    (L rho delta Delta : ℝ) (hL : 0 < L) (hd : 0 < delta) (hD : 0 ≤ Delta) (w : E)
    (g : E → ℝ) (hg : Legal L rho Delta g) :
    let r := run L delta (oracle g) (totalFuel L delta Delta) (0,w)
    r.1.1 = 2 ∧ ‖gradient g r.1.2‖ ≤ delta ∧ r.2 ≤ ⌈4*Delta*L/delta^2⌉₊+2 :=
  globally_correct_with_uniform_finite_budget g L delta Delta (sInf (Set.range g))
    hL hd hD (hg.smooth.differentiable (by simp)) hg.gradient_lipschitz hg.lower_bound hg.gap w

end
end OriginalGloballyCorrectStationaryVerifier


open MeasureTheory
open scoped ContDiff Topology

namespace OriginalFixedInstanceGloballyCorrectRefutation
open OriginalGloballyCorrectStationaryVerifier
noncomputable section
set_option maxHeartbeats 4000000

variable {E Seed : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace (AllJet E)] [BorelSpace (AllJet E)] [MeasurableSpace Seed]

/-- A finite deterministic Borel machine is a randomized local algorithm which
ignores its independent seed. Its code contains no function/oracle argument. -/
structure Algorithm where
  machine : Machine (E := E)
  initial : State E
  fuel : ℕ

def execution (A : Algorithm (E := E)) (f : E → ℝ) : E × ℕ :=
  let r := machineRun A.machine (oracle f) A.fuel A.initial
  (A.machine.value r.1,r.2)

def seededExecution (A : Algorithm (E := E)) (f : E → ℝ) (_seed : Seed) : E × ℕ :=
  execution A f

theorem seeded_execution_measurable (A : Algorithm (E := E)) (f : E → ℝ) :
    Measurable (seededExecution (Seed := Seed) A f) := measurable_const

def verifierAlgorithm (L delta Delta : ℝ) (w : E) : Algorithm (E := E) where
  machine := checkedMachine L delta
  initial := (0,w)
  fuel := totalFuel L delta Delta

theorem actual_verifier_execution (L delta Delta : ℝ) (w : E) (f : E → ℝ) :
    execution (verifierAlgorithm L delta Delta w) f =
      ((run L delta (oracle f) (totalFuel L delta Delta) (0,w)).1.2,
       (run L delta (oracle f) (totalFuel L delta Delta) (0,w)).2) := by
  unfold execution verifierAlgorithm
  rw [checked_machine_is_actual_run]
  rfl

/-- Global correctness and a common finite worst-case bound are separate from
how many queries the program actually executes on one specified instance. -/
def GloballyCorrect (L rho delta Delta : ℝ) (A : Algorithm (E := E)) : Prop :=
  ∀ g : E → ℝ, Legal L rho Delta g →
    ‖gradient g (execution A g).1‖ ≤ delta ∧
      (execution A g).2 ≤ ⌈4*Delta*L/delta^2⌉₊+2

theorem verification_fallback_is_globally_correct
    (L rho delta Delta : ℝ) (hL : 0 < L) (hd : 0 < delta) (hD : 0 ≤ Delta) (w : E) :
    GloballyCorrect L rho delta Delta (verifierAlgorithm L delta Delta w) := by
  intro g hg
  rw [actual_verifier_execution]
  have h := uniform_global_correctness_on_original_class L rho delta Delta hL hd hD w g hg
  exact ⟨h.2.1,h.2.2⟩

theorem verification_fallback_one_call_on_selected_function
    (L delta Delta : ℝ) (f : E → ℝ) (w : E) (hw : ‖gradient f w‖ ≤ delta) :
    execution (verifierAlgorithm L delta Delta w) f = (w,1) := by
  rw [actual_verifier_execution,totalFuel,selected_function_exactly_one_call L delta f w hw]

/-- Every legal fixed function has a member of the globally correct Borel
algorithm class which succeeds on that fixed function after one actual query.
The code constant w may be chosen after fixing f; the program still verifies it
against each queried oracle and falls back correctly for every other g. -/
theorem each_fixed_function_has_globally_correct_one_query_algorithm
    (P : Measure Seed) [IsProbabilityMeasure P]
    (L rho delta Delta T : ℝ) (hL : 0 < L) (hd : 0 < delta) (hD : 0 ≤ Delta) (hT : 2 ≤ T)
    (f : E → ℝ) (hf : Legal L rho Delta f) :
    ∃ (w : E) (A : Algorithm (E := E)),
      A = verifierAlgorithm L delta Delta w ∧
      GloballyCorrect L rho delta Delta A ∧
      execution A f = (w,1) ∧
      Measurable (seededExecution (Seed := Seed) A f) ∧
      P {seed : Seed | ‖gradient f (seededExecution A f seed).1‖ ≤ delta ∧
        ((seededExecution A f seed).2 : ℝ) < T} = 1 := by
  obtain ⟨w,hw⟩ := OriginalAudit.exists_small_gradient f L hL
    (hf.smooth.differentiable (by norm_num))
    hf.gradient_lipschitz ⟨sInf (Set.range f),hf.lower_bound⟩ delta hd
  let A := verifierAlgorithm L delta Delta w
  have he : execution A f = (w,1) :=
    verification_fallback_one_call_on_selected_function L delta Delta f w hw
  refine ⟨w,A,rfl,verification_fallback_is_globally_correct L rho delta Delta hL hd hD w,
    he,seeded_execution_measurable A f,?_⟩
  have hevent : {seed : Seed | ‖gradient f (seededExecution A f seed).1‖ ≤ delta ∧
      ((seededExecution A f seed).2 : ℝ) < T} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro seed
    simp only [seededExecution,he,Prod.fst,Prod.snd,Nat.cast_one]
    exact ⟨hw,by linarith⟩
  rw [hevent]
  exact measure_univ

/-- Negation of the literal fixed-function, all-algorithms lower bound. This is
an instance-wise query statement. It does not assert that the program's common
worst-case budget over g is below T, and does not negate a minimax lower bound. -/
theorem no_fixed_function_hard_for_every_globally_correct_borel_algorithm
    (P : Measure Seed) [IsProbabilityMeasure P]
    (L rho delta Delta T : ℝ) (hL : 0 < L) (hd : 0 < delta) (hD : 0 ≤ Delta) (hT : 2 ≤ T) :
    ¬ ∃ f : E → ℝ, Legal L rho Delta f ∧
      ∀ A : Algorithm (E := E), GloballyCorrect L rho delta Delta A →
        P {seed : Seed | ‖gradient f (seededExecution A f seed).1‖ ≤ delta ∧
          ((seededExecution A f seed).2 : ℝ) < T} ≤ (2/3 : ENNReal) := by
  rintro ⟨f,hf,hhard⟩
  obtain ⟨w,A,hA,hglobal,he,hm,hs⟩ :=
    each_fixed_function_has_globally_correct_one_query_algorithm P L rho delta Delta T hL hd hD hT f hf
  have hbad := hhard A hglobal
  rw [hs] at hbad
  have hfinite : (2/3 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hreal := ENNReal.toReal_mono hfinite hbad
  norm_num at hreal

section LiteralEuclidean
local instance euclideanMeasurableSpace (d : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
  borel (EuclideanSpace ℝ (Fin d))
local instance euclideanBorelSpace (d : ℕ) : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
local instance allJetEuclideanMeasurableSpace (d : ℕ) :
    MeasurableSpace (AllJet (EuclideanSpace ℝ (Fin d))) :=
  borel (AllJet (EuclideanSpace ℝ (Fin d)))
local instance allJetEuclideanBorelSpace (d : ℕ) :
    BorelSpace (AllJet (EuclideanSpace ℝ (Fin d))) := ⟨rfl⟩

/-- Original Euclidean dimensions and positive parameter scope. Both the
functions and all infinite derivative replies carry their actual Borel spaces.
The universal hard function does not exist in any finite dimension. -/
theorem no_single_euclidean_function_hard_for_all_globally_correct_algorithms
    (P : Measure Seed) [IsProbabilityMeasure P]
    (L rho delta Delta T : ℝ) (hL : 0 < L) (_hr : 0 < rho)
    (hd : 0 < delta) (hD : 0 < Delta) (hT : 2 ≤ T) :
    ¬ ∃ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), Legal L rho Delta f ∧
      ∀ A : Algorithm (E := EuclideanSpace ℝ (Fin d)), GloballyCorrect L rho delta Delta A →
        P {seed : Seed | ‖gradient f (seededExecution A f seed).1‖ ≤ delta ∧
          ((seededExecution A f seed).2 : ℝ) < T} ≤ (2/3 : ENNReal) := by
  rintro ⟨d,f,hf,hhard⟩
  exact no_fixed_function_hard_for_every_globally_correct_borel_algorithm
    (E := EuclideanSpace ℝ (Fin d)) P L rho delta Delta T hL hd hD.le hT ⟨f,hf,hhard⟩

end LiteralEuclidean
end
end OriginalFixedInstanceGloballyCorrectRefutation


open MeasureTheory

namespace OriginalDimensionUniformVerifierRefutation
open OriginalGloballyCorrectStationaryVerifier OriginalFixedInstanceGloballyCorrectRefutation
noncomputable section
set_option maxHeartbeats 4000000

local instance euclideanMeasurableSpace (d : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
  borel (EuclideanSpace ℝ (Fin d))
local instance euclideanBorelSpace (d : ℕ) : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
local instance allJetEuclideanMeasurableSpace (d : ℕ) :
    MeasurableSpace (AllJet (EuclideanSpace ℝ (Fin d))) :=
  borel (AllJet (EuclideanSpace ℝ (Fin d)))
local instance allJetEuclideanBorelSpace (d : ℕ) :
    BorelSpace (AllJet (EuclideanSpace ℝ (Fin d))) := ⟨rfl⟩

abbrev AlgorithmFamily := (d : ℕ) → Algorithm (E := EuclideanSpace ℝ (Fin d))

def GloballyCorrectInEveryDimension (L rho delta Delta : ℝ) (A : AlgorithmFamily) : Prop :=
  ∀ d : ℕ, GloballyCorrect L rho delta Delta (A d)

/-- The finite program may store the code constant w in its designated
Euclidean dimension. In all other dimensions it verifies zero first. This is a
single algorithm family, with the same finite fallback budget in every dimension. -/
def codePoint (targetDimension : ℕ) (w : EuclideanSpace ℝ (Fin targetDimension))
    (d : ℕ) : EuclideanSpace ℝ (Fin d) :=
  if h : d = targetDimension then h.symm ▸ w else 0

def verificationFamily (L delta Delta : ℝ) (targetDimension : ℕ)
    (w : EuclideanSpace ℝ (Fin targetDimension)) : AlgorithmFamily :=
  fun d => verifierAlgorithm L delta Delta (codePoint targetDimension w d)

theorem verification_family_globally_correct_in_every_dimension
    (L rho delta Delta : ℝ) (hL : 0 < L) (hd : 0 < delta) (hD : 0 ≤ Delta)
    (targetDimension : ℕ) (w : EuclideanSpace ℝ (Fin targetDimension)) :
    GloballyCorrectInEveryDimension L rho delta Delta
      (verificationFamily L delta Delta targetDimension w) := by
  intro d
  exact verification_fallback_is_globally_correct L rho delta Delta hL hd hD _

theorem selected_dimension_execution_is_one_query
    (L delta Delta : ℝ) (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖gradient f w‖ ≤ delta) :
    execution (verificationFamily L delta Delta d w d) f = (w,1) := by
  simpa [verificationFamily,codePoint] using
    verification_fallback_one_call_on_selected_function L delta Delta f w hw

variable {Seed : Type*} [MeasurableSpace Seed]

/-- A complete literal fixed-instance refutation with a globally correct
algorithm family covering every finite dimension and a common dimension-free
worst-case finite call bound. The selected instance itself costs exactly one
query; this theorem does not place that common worst-case bound below T. -/
theorem no_single_function_hard_for_every_dimension_uniform_globally_correct_algorithm
    (P : Measure Seed) [IsProbabilityMeasure P]
    (L rho delta Delta T : ℝ) (hL : 0 < L) (_hr : 0 < rho)
    (hd : 0 < delta) (hD : 0 < Delta) (hT : 2 ≤ T) :
    ¬ ∃ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), Legal L rho Delta f ∧
      ∀ A : AlgorithmFamily, GloballyCorrectInEveryDimension L rho delta Delta A →
        P {seed : Seed | ‖gradient f (seededExecution (A d) f seed).1‖ ≤ delta ∧
          ((seededExecution (A d) f seed).2 : ℝ) < T} ≤ (2/3 : ENNReal) := by
  rintro ⟨d,f,hf,hhard⟩
  obtain ⟨w,hw⟩ := OriginalAudit.exists_small_gradient f L hL
    (hf.smooth.differentiable (by norm_num)) hf.gradient_lipschitz
    ⟨sInf (Set.range f),hf.lower_bound⟩ delta hd
  let A := verificationFamily L delta Delta d w
  have hglobal : GloballyCorrectInEveryDimension L rho delta Delta A :=
    verification_family_globally_correct_in_every_dimension L rho delta Delta hL hd hD.le d w
  have he : execution (A d) f = (w,1) :=
    selected_dimension_execution_is_one_query L delta Delta d f w hw
  have hevent : {seed : Seed | ‖gradient f (seededExecution (A d) f seed).1‖ ≤ delta ∧
      ((seededExecution (A d) f seed).2 : ℝ) < T} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro seed
    simp only [seededExecution,he,Nat.cast_one]
    exact ⟨hw,by linarith⟩
  have hbad := hhard A hglobal
  rw [hevent,measure_univ] at hbad
  have hfinite : (2/3 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hreal := ENNReal.toReal_mono hfinite hbad
  norm_num at hreal

end
end OriginalDimensionUniformVerifierRefutation


open MeasureTheory

namespace OriginalLiteralSingleLowerFullQuantifiers
open OriginalGloballyCorrectStationaryVerifier OriginalFixedInstanceGloballyCorrectRefutation
  OriginalDimensionUniformVerifierRefutation
noncomputable section

local instance euclideanMeasurableSpace (d : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
  borel (EuclideanSpace ℝ (Fin d))
local instance euclideanBorelSpace (d : ℕ) : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
local instance allJetEuclideanMeasurableSpace (d : ℕ) :
    MeasurableSpace (AllJet (EuclideanSpace ℝ (Fin d))) :=
  borel (AllJet (EuclideanSpace ℝ (Fin d)))
local instance allJetEuclideanBorelSpace (d : ℕ) :
    BorelSpace (AllJet (EuclideanSpace ℝ (Fin d))) := ⟨rfl⟩

def threshold (c L rho delta Delta : ℝ) : ℝ :=
  c*Delta*min (L/delta^2) (Real.sqrt rho / delta^(3/2:ℝ))

/-- Even after dropping the original dimension upper bound, the literal
universal-constants/fixed-function/all-globally-correct-algorithms assertion is
false. This is not the corrected algorithm-dependent minimax assertion. -/
theorem no_original_literal_universal_constants
    {Seed : Type*} [MeasurableSpace Seed] (P : Measure Seed) [IsProbabilityMeasure P] :
    ¬ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ L rho delta Delta : ℝ, 0 < L → 0 < rho → 0 < delta → 0 < Delta →
        C ≤ threshold c L rho delta Delta →
        ∃ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), Legal L rho Delta f ∧
          ∀ A : AlgorithmFamily, GloballyCorrectInEveryDimension L rho delta Delta A →
            P {seed : Seed | ‖gradient f (seededExecution (A d) f seed).1‖ ≤ delta ∧
              ((seededExecution (A d) f seed).2 : ℝ) < threshold c L rho delta Delta} ≤
                (2/3 : ENNReal) := by
  rintro ⟨c,C,hc,hC,hhard⟩
  let Delta := max C 2 / c
  have hm : 0 < max C (2:ℝ) := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_right _ _)
  have hD : 0 < Delta := div_pos hm hc
  have ht : threshold c 1 1 1 Delta = max C 2 := by
    dsimp [threshold,Delta]
    simp only [one_pow,one_div,Real.sqrt_one,Real.one_rpow,div_one,min_self,mul_one]
    field_simp
  have hCbound : C ≤ threshold c 1 1 1 Delta := by rw [ht]; exact le_max_left _ _
  have hT : 2 ≤ threshold c 1 1 1 Delta := by rw [ht]; exact le_max_right _ _
  have hF := hhard 1 1 1 Delta (by norm_num) (by norm_num) (by norm_num) hD hCbound
  exact no_single_function_hard_for_every_dimension_uniform_globally_correct_algorithm
    P 1 1 1 Delta (threshold c 1 1 1 Delta) (by norm_num) (by norm_num)
      (by norm_num) hD hT hF

end
end OriginalLiteralSingleLowerFullQuantifiers
end PaperAudit.SingleLowerCounterexample
