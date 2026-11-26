import Mathlib

namespace PaperAudit.WarmUniformCounterexample




namespace OriginalWarmResistingProgram

noncomputable section

/-- A finite adaptive exact-oracle algorithm. The public input is fixed before this tree
is chosen; every reply may affect every later query and the final, unqueried output. -/
inductive Program (Q Reply Out : Type*) : ℕ → Type _
  | pure {n : ℕ} (value : Out) : Program Q Reply Out n
  | ask {n : ℕ} (query : Q) (next : Reply → Program Q Reply Out n) :
      Program Q Reply Out (n + 1)

def execute {Q Reply Out : Type*} {n : ℕ} (oracle : Q → Reply) :
    Program Q Reply Out n → Out
  | .pure value => value
  | .ask query next => execute oracle (next (oracle query))

/-- A localized refinement scheme. Its hypotheses express only actual support and
interval geometry, rather than any lower-bound conclusion. -/
structure Scheme (S Q Reply Out : Type*) where
  oracle : S → Q → Reply
  queryCoordinate : Q → ℝ
  outputCoordinate : Out → ℝ
  center : S → ℝ
  radius : S → ℝ
  ratio : ℝ
  ratio_pos : 0 < ratio
  ratio_small : ratio ≤ 1 / 16
  radius_pos : ∀ s, 0 < radius s
  refine : S → ℝ → S
  radius_refine : ∀ s x, radius (refine s x) = ratio * radius s
  center_refine : ∀ s x, |center (refine s x) - center s| ≤ 4 * ratio * radius s
  far_refine : ∀ s x, 4 * ratio * radius s ≤ |x - center (refine s x)|
  oracle_refine : ∀ s x query, radius s ≤ |queryCoordinate query - center s| →
    oracle (refine s x) query = oracle s query

variable {S Q Reply Out : Type*} (C : Scheme S Q Reply Out)

theorem outside_refined_interval (s : S) (x z : ℝ)
    (hz : C.radius s ≤ |z - C.center s|) :
    C.radius (C.refine s x) ≤ |z - C.center (C.refine s x)| := by
  have ht := abs_add_le (z - C.center (C.refine s x))
    (C.center (C.refine s x) - C.center s)
  rw [sub_add_sub_cancel] at ht
  rw [C.radius_refine]
  have hr := C.radius_pos s
  have hq := C.ratio_small
  have hs := C.center_refine s x
  nlinarith

theorem refined_query_is_outside (s : S) (x : ℝ) :
    C.radius (C.refine s x) ≤ |x - C.center (C.refine s x)| := by
  rw [C.radius_refine]
  have h := C.far_refine s x
  have hq := C.ratio_pos
  have hr := C.radius_pos s
  nlinarith

def resist {n : ℕ} (p : Program Q Reply Out n) (s : S) : S :=
  match p with
  | .pure value => C.refine s (C.outputCoordinate value)
  | .ask query next =>
      let s' := C.refine s (C.queryCoordinate query)
      resist (next (C.oracle s' query)) s'

/-- The returned state is one fixed oracle instance. Executing the original adaptive
algorithm against that instance exactly replays the constructed replies. No restriction
on where the algorithm queries, and no query requirement on its output, is imposed. -/
theorem resist_fixed_instance {n : ℕ} (p : Program Q Reply Out n) (s : S) :
    (∀ query, C.radius s ≤ |C.queryCoordinate query - C.center s| →
      C.oracle (resist C p s) query = C.oracle s query) ∧
    4 * C.ratio ^ (n + 1) * C.radius s ≤
      |C.outputCoordinate (execute (C.oracle (resist C p s)) p) -
        C.center (resist C p s)| := by
  induction p generalizing s with
  | @pure n value =>
      constructor
      · intro query hquery
        exact C.oracle_refine s (C.outputCoordinate value) query hquery
      · change 4 * C.ratio ^ (n + 1) * C.radius s ≤
          |C.outputCoordinate value - C.center (C.refine s (C.outputCoordinate value))|
        have hp : C.ratio ^ (n + 1) ≤ C.ratio :=
          pow_le_of_le_one C.ratio_pos.le (by linarith [C.ratio_small]) (by omega)
        have h := C.far_refine s (C.outputCoordinate value)
        nlinarith [C.radius_pos s]
  | @ask n query next ih =>
      let s' := C.refine s (C.queryCoordinate query)
      let answer := C.oracle s' query
      have hrec := ih answer s'
      have hquery : C.oracle (resist C (next answer) s') query = answer :=
        hrec.1 query (refined_query_is_outside C s (C.queryCoordinate query))
      constructor
      · intro query' hquery'
        change C.oracle (resist C (next answer) s') query' = C.oracle s query'
        rw [hrec.1 query' (outside_refined_interval C s (C.queryCoordinate query)
          (C.queryCoordinate query') hquery')]
        exact C.oracle_refine s (C.queryCoordinate query) query' hquery'
      · change 4 * C.ratio ^ (n + 1 + 1) * C.radius s ≤
          |C.outputCoordinate (execute (C.oracle (resist C (next answer) s'))
            (.ask query next)) - C.center (resist C (next answer) s')|
        simp only [execute, hquery]
        have hh := hrec.2
        change 4 * C.ratio ^ (n + 1) * C.radius (C.refine s
          (C.queryCoordinate query)) ≤ _ at hh
        rw [C.radius_refine] at hh
        rw [pow_succ]
        nlinarith


/-- Even an early-stopping algorithm performs at most its fuel plus the final
output-avoidance refinement; this is a lower bound on the remaining interval radius. -/
theorem resist_radius_lower_bound {n : ℕ} (p : Program Q Reply Out n) (s : S) :
    C.ratio ^ (n + 1) * C.radius s ≤ C.radius (resist C p s) := by
  induction p generalizing s with
  | @pure n value =>
      change C.ratio ^ (n + 1) * C.radius s ≤ C.radius (C.refine s (C.outputCoordinate value))
      rw [C.radius_refine]
      exact mul_le_mul_of_nonneg_right
        (pow_le_of_le_one C.ratio_pos.le (by linarith [C.ratio_small]) (by omega))
        (C.radius_pos s).le
  | @ask n query next ih =>
      let s' := C.refine s (C.queryCoordinate query)
      have h := ih (C.oracle s' query) s'
      change C.ratio ^ (n + 1 + 1) * C.radius s ≤
        C.radius (resist C (next (C.oracle s' query)) s')
      calc
        _ = C.ratio ^ (n + 1) * C.radius s' := by
          dsimp [s']
          rw [C.radius_refine, pow_succ]
          ring
        _ ≤ _ := h

end
end OriginalWarmResistingProgram


open scoped ContDiff Topology

namespace OriginalWarmCompactPotential

noncomputable section

/-- An explicit smooth compactly supported potential with an exactly linear core. -/
def potential (t : ℝ) : ℝ :=
  t * (1 - Real.smoothTransition (4 * (t ^ 2 - 9 / 16)))

theorem potential_smooth : ContDiff ℝ ∞ potential := by unfold potential; fun_prop

theorem potential_linear_germ (t : ℝ) (ht : |t| ≤ 1 / 2) :
    potential =ᶠ[𝓝 t] (fun u => u) := by
  have ht' : t ^ 2 < 9 / 16 := by
    have h := (abs_le.mp ht)
    nlinarith
  have hn : ∀ᶠ u : ℝ in 𝓝 t, u ^ 2 < 9 / 16 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds ht'
  filter_upwards [hn] with u hu
  have hz := Real.smoothTransition.zero_of_nonpos (show 4 * (u ^ 2 - 9 / 16) ≤ 0 by linarith only [hu])
  simp only [potential, hz, sub_zero, mul_one]

theorem potential_zero_germ (t : ℝ) (ht : 1 ≤ |t|) :
    potential =ᶠ[𝓝 t] (fun _ => 0) := by
  have ht' : 13 / 16 < t ^ 2 := by
    have h := sq_abs t
    nlinarith [sq_nonneg (|t| - 1)]
  have hn : ∀ᶠ u : ℝ in 𝓝 t, 13 / 16 < u ^ 2 :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds ht'
  filter_upwards [hn] with u hu
  have hz := Real.smoothTransition.one_of_one_le (show 1 ≤ 4 * (u ^ 2 - 9 / 16) by linarith only [hu])
  simp only [potential, hz, sub_self, mul_zero]

theorem potential_global_derivative_bounds :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ j : ℕ, j ≤ 3 → ∀ t : ℝ,
      |iteratedDeriv j potential t| ≤ K := by
  have hc : ∀ j : Fin 4, Continuous (iteratedDeriv j.val potential) := by
    intro j
    exact potential_smooth.continuous_iteratedDeriv j.val (by exact_mod_cast (show (j.val : ℕ∞) ≤ ⊤ from le_top))
  have he : ∀ j : Fin 4, ∃ K : ℝ, ∀ t : ℝ,
      |iteratedDeriv j.val potential t| ≤ K := by
    intro j
    obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn
      (hc j).continuousOn
    refine ⟨max K 0, ?_⟩
    intro t
    by_cases ht : |t| ≤ 1
    · have hh := hK t (abs_le.mp ht)
      have hh' : |iteratedDeriv j.val potential t| ≤ K := by simpa only [Real.norm_eq_abs] using hh
      exact hh'.trans (le_max_left _ _)
    · have heq := (potential_zero_germ t (le_of_not_ge ht)).iteratedDeriv_eq j.val
      rw [heq]
      by_cases hj : j.val = 0
      · simp [hj]
      · simp [iteratedDeriv_const, hj]
  choose Ks hKs using he
  let K := 1 + ∑ j, max (Ks j) 0
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_right _ _))
  · intro j hj t
    let jj : Fin 4 := ⟨j, by omega⟩
    have hsum := Finset.single_le_sum (f := fun k : Fin 4 => max (Ks k) 0)
      (fun k _ => le_max_right _ _) (Finset.mem_univ jj)
    exact (hKs jj t).trans ((le_max_left _ _).trans (hsum.trans (by dsimp [K]; linarith)))

/-- The actual potential used in one oracle-preserving refinement. -/
def bump (q sign m w : ℝ) (u : ℝ) : ℝ :=
  -20 * sign * q * w ^ 2 * potential ((u - m) / w)

theorem bump_smooth (q sign m w : ℝ) : ContDiff ℝ ∞ (bump q sign m w) := by
  unfold bump
  exact contDiff_const.mul (potential_smooth.comp (by fun_prop))

theorem bump_derivative (q sign m w u : ℝ) (n : ℕ) :
    iteratedDeriv n (bump q sign m w) u =
      -20 * sign * q * w ^ 2 * (w⁻¹) ^ n *
        iteratedDeriv n potential ((u - m) / w) := by
  unfold bump
  rw [iteratedDeriv_const_mul_field]
  have heq : (fun z : ℝ => potential ((z - m) / w)) =
      fun z => potential (w⁻¹ * (z + -m)) := by funext z; congr 1; ring
  rw [heq]
  change -20 * sign * q * w ^ 2 *
    iteratedDeriv n (fun z => (fun v => potential (w⁻¹ * v)) (z + -m)) u = _
  rw [congrFun (iteratedDeriv_comp_add_const (f := fun v => potential (w⁻¹ * v)) (s := -m) (n := n)) u]
  rw [iteratedDeriv_comp_const_mul (potential_smooth.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)))]
  simp only
  rw [show w⁻¹ * (u + -m) = (u - m) / w by ring]
  ring

theorem bump_zero_germ (q sign m w u : ℝ) (hw : 0 < w) (hu : w ≤ |u - m|) :
    bump q sign m w =ᶠ[𝓝 u] (fun _ => 0) := by
  have ht : 1 ≤ |(u - m) / w| := by
    rw [abs_div, abs_of_pos hw]
    exact (le_div_iff₀ hw).mpr (by simpa using hu)
  have h := (potential_zero_germ ((u - m) / w) ht).comp_tendsto
    (show Filter.Tendsto (fun z : ℝ => (z - m) / w) (𝓝 u) (𝓝 ((u - m) / w)) by exact (show Continuous (fun z : ℝ => (z - m) / w) by fun_prop).continuousAt)
  filter_upwards [h] with z hz
  simp only [Function.comp_apply] at hz
  simp only [bump, hz, mul_zero]

theorem bump_linear_germ (q sign m w u : ℝ) (hw : 0 < w)
    (hu : |u - m| ≤ w / 2) :
    bump q sign m w =ᶠ[𝓝 u] (fun z => -20 * sign * q * w * (z - m)) := by
  have ht : |(u - m) / w| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hw]
    exact (div_le_iff₀ hw).mpr (by linarith only [hu])
  have h := (potential_linear_germ ((u - m) / w) ht).comp_tendsto
    (show Filter.Tendsto (fun z : ℝ => (z - m) / w) (𝓝 u) (𝓝 ((u - m) / w)) by exact (show Continuous (fun z : ℝ => (z - m) / w) by fun_prop).continuousAt)
  filter_upwards [h] with z hz
  simp only [Function.comp_apply] at hz
  dsimp [bump]
  rw [hz]
  field_simp
  <;> ring

end
end OriginalWarmCompactPotential


open scoped ContDiff Topology

namespace OriginalWarmRefinementState

open OriginalWarmCompactPotential

noncomputable section

def polynomial (m b u : ℝ) : ℝ := u ^ 2 / 2 - 5 * m * u + b

theorem polynomial_deriv (m b u : ℝ) : deriv (polynomial m b) u = u - 5 * m := by
  apply HasDerivAt.deriv
  convert! ((((hasDerivAt_id u).pow 2).div_const 2).sub
    ((hasDerivAt_id u).const_mul (5 * m))).add_const b using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

theorem polynomial_jets (m b u : ℝ) :
    iteratedDeriv 2 (polynomial m b) u = 1 ∧
    iteratedDeriv 3 (polynomial m b) u = 0 := by
  have h1 : deriv (polynomial m b) = fun u => u - 5 * m := by funext u; exact polynomial_deriv m b u
  have h2 : deriv (fun u : ℝ => u - 5 * m) = fun _ => 1 := by funext u; simp
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, h1, h2, deriv_const]
  norm_num

theorem bump_second_bound (K q sign m w u : ℝ) (hw : 0 < w)
    (hq : 0 ≤ q) (hs : |sign| = 1)
    (hK : ∀ t, |iteratedDeriv 2 potential t| ≤ K) :
    |iteratedDeriv 2 (bump q sign m w) u| ≤ 20 * q * K := by
  rw [bump_derivative]
  have he : -20 * sign * q * w ^ 2 * w⁻¹ ^ 2 = -20 * sign * q := by
    field_simp
    <;> ring
  rw [he, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 20),
    hs, abs_of_nonneg hq]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hK ((u - m) / w))
    (show 0 ≤ 20 * q by positivity)

theorem bump_third_bound (K q sign m w u : ℝ) (hw : 0 < w)
    (hq : 0 ≤ q) (hs : |sign| = 1)
    (hK : ∀ t, |iteratedDeriv 3 potential t| ≤ K) :
    |iteratedDeriv 3 (bump q sign m w) u| ≤ 20 * q * K / w := by
  rw [bump_derivative]
  have he : -20 * sign * q * w ^ 2 * w⁻¹ ^ 3 = -20 * sign * q / w := by
    field_simp
    <;> ring
  rw [he, abs_mul, abs_div, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 20), hs, abs_of_nonneg hq, abs_of_pos hw]
  have hh := mul_le_mul_of_nonneg_left (hK ((u - m) / w))
    (show 0 ≤ 20 * q / w by positivity)
  convert! hh using 1 <;> ring

/-- All fields describe actual derivatives of one smooth scalar function. The third
bound scales with the current radius; it is made uniformly one after finitely many
refinements by choosing the initial radius in advance. -/
structure State (q K a : ℝ) where
  function : ℝ → ℝ
  center : ℝ
  radius : ℝ
  offset : ℝ
  smooth : ContDiff ℝ ∞ function
  radius_pos : 0 < radius
  initial_outside : radius ≤ |a - center|
  initial_value : function a = 0
  initial_derivative : deriv function a = 0
  local_polynomial : ∀ u, |u - center| < radius → function u = polynomial center offset u
  second_bound : ∀ u, |iteratedDeriv 2 function u - 1| ≤ 1 / 2
  third_bound : ∀ u, |iteratedDeriv 3 function u| ≤ 20 * q * K / radius

variable {q K a : ℝ}

theorem local_polynomial_germ (s : State q K a) (u : ℝ) (hu : |u - s.center| < s.radius) :
    s.function =ᶠ[𝓝 u] polynomial s.center s.offset := by
  have hn : ∀ᶠ z : ℝ in 𝓝 u, |z - s.center| < s.radius :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds hu
  filter_upwards [hn] with z hz
  exact s.local_polynomial z hz

def signChoice (m x : ℝ) : ℝ := if x ≤ m then 1 else -1

theorem abs_signChoice (m x : ℝ) : |signChoice m x| = 1 := by
  unfold signChoice
  split_ifs <;> norm_num

theorem far_signChoice (m x w q : ℝ) (hw : 0 ≤ w) (hq : 0 ≤ q) :
    4 * q * w ≤ |x - (m + 4 * signChoice m x * q * w)| := by
  unfold signChoice
  split_ifs with h
  · rw [abs_of_nonpos (by nlinarith)]
    nlinarith
  · rw [abs_of_nonneg (by nlinarith)]
    nlinarith

theorem shifted_child_inside (m w q sign u : ℝ) (hw : 0 < w) (hq : 0 < q)
    (hsmall : q ≤ 1 / 16) (hs : |sign| = 1)
    (hu : |u - (m + 4 * sign * q * w)| < q * w) :
    |u - m| ≤ w / 2 := by
  have ht := abs_add_le (u - (m + 4 * sign * q * w)) (4 * sign * q * w)
  have ha : |4 * sign * q * w| = 4 * q * w := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      hs, abs_of_pos hq, abs_of_pos hw]
    ring
  rw [show u - (m + 4 * sign * q * w) + 4 * sign * q * w = u - m by ring, ha] at ht
  nlinarith


def refinedFunction (s : State q K a) (x : ℝ) (u : ℝ) : ℝ :=
  s.function u + bump q (signChoice s.center x) s.center s.radius u

theorem refined_function_germ_outside (s : State q K a) (x u : ℝ)
    (hu : s.radius ≤ |u - s.center|) :
    refinedFunction s x =ᶠ[𝓝 u] s.function := by
  have h := bump_zero_germ q (signChoice s.center x) s.center s.radius u s.radius_pos hu
  filter_upwards [h] with z hz
  simp only [refinedFunction, hz, add_zero]

/-- One actual compact potential refinement, with no accumulation of the second-jet
perturbation: inside the support the previous function is exactly quadratic. -/
def refine (hq : 0 < q) (hsmall : q ≤ 1 / 16) (hK : 0 ≤ K)
    (hcurv : 20 * q * K ≤ 1 / 2)
    (hprofile : ∀ j : ℕ, j ≤ 3 → ∀ t : ℝ, |iteratedDeriv j potential t| ≤ K)
    (s : State q K a) (x : ℝ) : State q K a := by
  let sign := signChoice s.center x
  have hs : |sign| = 1 := abs_signChoice _ _
  have hq1 : q ≤ 1 := by linarith only [hsmall]
  have hw := s.radius_pos
  have htarget : 20 * q * K / s.radius ≤ 20 * q * K / (q * s.radius) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_of_le_one_left s.radius_pos.le hq1
  refine
    { function := refinedFunction s x
      center := s.center + 4 * sign * q * s.radius
      radius := q * s.radius
      offset := s.offset + 20 * sign * q * s.radius * s.center
      smooth := s.smooth.add (bump_smooth _ _ _ _)
      radius_pos := mul_pos hq s.radius_pos
      initial_outside := ?_
      initial_value := ?_
      initial_derivative := ?_
      local_polynomial := ?_
      second_bound := ?_
      third_bound := ?_ }
  · have ht := abs_add_le (a - (s.center + 4 * sign * q * s.radius))
        (4 * sign * q * s.radius)
    have ha : |4 * sign * q * s.radius| = 4 * q * s.radius := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        hs, abs_of_pos hq, abs_of_pos s.radius_pos]
      ring
    rw [show a - (s.center + 4 * sign * q * s.radius) + 4 * sign * q * s.radius =
      a - s.center by ring, ha] at ht
    have h := s.initial_outside
    nlinarith [s.radius_pos]
  · exact ((refined_function_germ_outside s x a s.initial_outside).eq_of_nhds).trans s.initial_value
  · rw [(refined_function_germ_outside s x a s.initial_outside).deriv_eq]
    exact s.initial_derivative
  · intro u hu
    have hin := shifted_child_inside s.center s.radius q sign u s.radius_pos hq hsmall hs hu
    have hold := s.local_polynomial u (lt_of_le_of_lt hin (by linarith [s.radius_pos]))
    have hb := (bump_linear_germ q sign s.center s.radius u s.radius_pos hin).eq_of_nhds
    change s.function u + bump q sign s.center s.radius u = _
    rw [hold, hb]
    dsimp [polynomial]
    ring
  · intro u
    by_cases hin : |u - s.center| < s.radius
    · have hpoly := (local_polynomial_germ s u hin).iteratedDeriv_eq 2
      have hb := bump_second_bound K q sign s.center s.radius u s.radius_pos hq.le hs
        (hprofile 2 (by omega))
      change |iteratedDeriv 2 (fun u => s.function u + bump q sign s.center s.radius u) u - 1| ≤ _
      rw [iteratedDeriv_fun_add (s.smooth.of_le (by decide)).contDiffAt
        ((bump_smooth q sign s.center s.radius).of_le (by decide)).contDiffAt,
        hpoly, (polynomial_jets _ _ _).1]
      simpa only [add_sub_cancel_left] using hb.trans hcurv
    · rw [(refined_function_germ_outside s x u (le_of_not_gt hin)).iteratedDeriv_eq 2]
      exact s.second_bound u
  · intro u
    by_cases hin : |u - s.center| < s.radius
    · have hpoly := (local_polynomial_germ s u hin).iteratedDeriv_eq 3
      have hb := bump_third_bound K q sign s.center s.radius u s.radius_pos hq.le hs
        (hprofile 3 (by omega))
      change |iteratedDeriv 3 (fun u => s.function u + bump q sign s.center s.radius u) u| ≤ _
      rw [iteratedDeriv_fun_add (s.smooth.of_le (by decide)).contDiffAt
        ((bump_smooth q sign s.center s.radius).of_le (by decide)).contDiffAt,
        hpoly, (polynomial_jets _ _ _).2, zero_add]
      exact hb.trans htarget
    · rw [(refined_function_germ_outside s x u (le_of_not_gt hin)).iteratedDeriv_eq 3]
      exact (s.third_bound u).trans htarget


/-- The common initial scalar instance. Every later refinement preserves the public
initial point a=-20w as a zero-valued stationary point. -/
def initial (q K w : ℝ) (hq : 0 ≤ q) (hK : 0 ≤ K) (hw : 0 < w) :
    State q K (-20 * w) := by
  let a := -20 * w
  refine
    { function := polynomial (a / 5) (a ^ 2 / 2)
      center := a / 5
      radius := w
      offset := a ^ 2 / 2
      smooth := by unfold polynomial; fun_prop
      radius_pos := hw
      initial_outside := ?_
      initial_value := ?_
      initial_derivative := ?_
      local_polynomial := fun _ _ => rfl
      second_bound := ?_
      third_bound := ?_ }
  · dsimp [a]
    rw [abs_of_nonpos (by linarith)]
    linarith
  · dsimp [polynomial, a]
    ring
  · rw [polynomial_deriv]
    dsimp [a]
    ring
  · intro u
    rw [(polynomial_jets _ _ _).1]
    norm_num
  · intro u
    rw [(polynomial_jets _ _ _).2, abs_zero]
    positivity

end
end OriginalWarmRefinementState


open scoped ContDiff Topology

namespace OriginalWarmSaddleOracle

noncomputable section

abbrev Space := WithLp 2 (ℝ × ℝ)
local instance : NormedSpace ℝ Space := inferInstance
local instance : ContinuousSMul ℝ Space := inferInstance

def point (u y : ℝ) : Space := WithLp.toLp 2 (u, y)
def saddle (f : ℝ → ℝ) (z : Space) : ℝ := f z.fst - z.snd ^ 2 / 2

def diagonal (a : ℝ) : Space →L[ℝ] Space :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap.comp
    ((a • WithLp.fstL 2 ℝ ℝ ℝ).prod (-WithLp.sndL 2 ℝ ℝ ℝ))

structure Answer where
  value : ℝ
  grad : Space
  hess : Space →L[ℝ] Space

def oracle (f : ℝ → ℝ) (z : Space) : Answer :=
  ⟨saddle f z, gradient (saddle f) z, fderiv ℝ (gradient (saddle f)) z⟩

theorem oracle_eq_of_scalar_germ (f g : ℝ → ℝ) (z : Space)
    (h : f =ᶠ[𝓝 z.fst] g) : oracle f z = oracle g z := by
  have he : saddle f =ᶠ[𝓝 z] saddle g := by
    have hc := h.comp_tendsto (WithLp.fstL 2 ℝ ℝ ℝ).continuous.continuousAt
    filter_upwards [hc] with w hw
    simp only [Function.comp_apply] at hw
    exact congrArg (fun v => v - w.snd ^ 2 / 2) hw
  have hvalue := he.eq_of_nhds
  have hgrad := he.gradient_eq
  have hhess := he.gradient.fderiv_eq (𝕜 := ℝ)
  change Answer.mk (saddle f z) (gradient (saddle f) z) (fderiv ℝ (gradient (saddle f)) z) =
    Answer.mk (saddle g z) (gradient (saddle g) z) (fderiv ℝ (gradient (saddle g)) z)
  rw [hvalue, hgrad, hhess]

theorem actual_gradient (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (z : Space) :
    HasGradientAt (saddle f) (point (deriv f z.fst) (-z.snd)) z := by
  have hu := ((hf.differentiable (by norm_num)) z.fst).hasDerivAt.hasFDerivAt.comp z
    (WithLp.fstL 2 ℝ ℝ ℝ).hasFDerivAt
  have hy := (((WithLp.sndL 2 ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2).const_mul (1 / 2 : ℝ)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hu.sub hy using 1
  · funext w
    change f w.fst - w.snd ^ 2 / 2 = f w.fst - (1 / 2 : ℝ) * w.snd ^ 2
    ring
  · ext v
    simp only [InnerProductSpace.toDual_apply_apply, WithLp.prod_inner_apply,
      Real.inner_apply, point, WithLp.toLp_fst, WithLp.toLp_snd,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, two_smul]
    change deriv f z.fst * v.fst + (-z.snd) * v.snd =
      v.fst * deriv f z.fst - (1 / 2 : ℝ) * ((z.snd ^ (2 - 1) + z.snd ^ (2 - 1)) * v.snd)
    ring

theorem actual_hessian (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (z : Space) :
    fderiv ℝ (gradient (saddle f)) z = diagonal (iteratedDeriv 2 f z.fst) := by
  have hgrad : gradient (saddle f) = fun w => point (deriv f w.fst) (-w.snd) :=
    funext (fun w => (actual_gradient f hf w).gradient)
  rw [hgrad]
  have hd : HasDerivAt (deriv f) (iteratedDeriv 2 f z.fst) z.fst := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      ((hf.differentiable_iteratedDeriv 1 (by norm_num)) z.fst).hasDerivAt
  have hu := hd.hasFDerivAt.comp z (WithLp.fstL 2 ℝ ℝ ℝ).hasFDerivAt
  have hy := (WithLp.sndL 2 ℝ ℝ ℝ).hasFDerivAt.neg (x := z)
  have hprod := hu.prodMk hy
  have hout := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp z hprod
  convert! hout.fderiv using 1
  · ext v
    apply (WithLp.ext_iff 2).mpr
    change (iteratedDeriv 2 f z.fst * v.fst, -v.snd) =
      (v.fst * iteratedDeriv 2 f z.fst, -v.snd)
    congr 1
    ring

end
end OriginalWarmSaddleOracle


open scoped ContDiff Topology

namespace OriginalWarmFiniteAdversary

open OriginalWarmCompactPotential OriginalWarmRefinementState OriginalWarmResistingProgram
  OriginalWarmSaddleOracle

noncomputable section

def scheme (q K a : ℝ) (hq : 0 < q) (hsmall : q ≤ 1 / 16) (hK : 0 ≤ K)
    (hcurv : 20 * q * K ≤ 1 / 2)
    (hprofile : ∀ j : ℕ, j ≤ 3 → ∀ t : ℝ, |iteratedDeriv j potential t| ≤ K) :
    Scheme (State q K a) Space Answer Space where
  oracle s := oracle s.function
  queryCoordinate z := z.fst
  outputCoordinate z := z.fst
  center s := s.center
  radius s := s.radius
  ratio := q
  ratio_pos := hq
  ratio_small := hsmall
  radius_pos s := s.radius_pos
  refine := OriginalWarmRefinementState.refine hq hsmall hK hcurv hprofile
  radius_refine _ _ := rfl
  center_refine s x := by
    change |s.center + 4 * signChoice s.center x * q * s.radius - s.center| ≤ 4 * q * s.radius
    rw [add_sub_cancel_left, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_signChoice,
      abs_of_pos hq, abs_of_pos s.radius_pos]
    simp
  far_refine s x := far_signChoice s.center x s.radius q s.radius_pos.le hq.le
  oracle_refine s x z hz := oracle_eq_of_scalar_germ _ _ z
    (refined_function_germ_outside s x z.fst hz)

/-- A deterministic algorithm may use the shared public initial input a without any
restriction. For each prescribed finite query budget, one fixed smooth scalar instance
preserves that exact input and defeats its real complete bundled-oracle execution. -/
theorem finite_exact_bundle_adversary (n : ℕ)
    (algorithm : ℝ → Program Space Answer Space n) :
    ∃ (a : ℝ) (f : ℝ → ℝ) (m : ℝ),
      ContDiff ℝ ∞ f ∧ f a = 0 ∧ deriv f a = 0 ∧
      (∀ u, |iteratedDeriv 2 f u - 1| ≤ 1 / 2) ∧
      (∀ u, |iteratedDeriv 3 f u| ≤ 1) ∧
      (∃ b w : ℝ, 0 < w ∧ ∀ u, |u - m| < w → f u = polynomial m b u) ∧
      1 < |(execute (oracle f) (algorithm a)).fst - m| := by
  obtain ⟨K, hK1, hprofile⟩ := potential_global_derivative_bounds
  have hK : 0 < K := by linarith only [hK1]
  let q : ℝ := 1 / (80 * (K + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hqsmall : q ≤ 1 / 16 := by
    dsimp [q]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hK1]
  have hcurv : 20 * q * K ≤ 1 / 2 := by
    dsimp [q]
    have he : 20 * (1 / (80 * (K + 1))) * K = K / (4 * (K + 1)) := by field_simp; ring
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hK1]
  let W : ℝ := 1 + 20 * K + 1 / q
  have hW : 0 < W := by dsimp [W]; positivity
  have hWbound : 20 * K ≤ W := by dsimp [W]; linarith [one_div_pos.mpr hq]
  let w : ℝ := W / q ^ n
  have hw : 0 < w := by dsimp [w]; positivity
  let a : ℝ := -20 * w
  let C := scheme q K a hq hqsmall hK.le hcurv hprofile
  let s0 : State q K a := initial q K w hq.le hK.le hw
  let sf := resist C (algorithm a) s0
  have hr := resist_radius_lower_bound C (algorithm a) s0
  have hdist := (resist_fixed_instance C (algorithm a) s0).2
  have he : q ^ (n + 1) * w = q * W := by
    dsimp [w]
    rw [pow_succ]
    field_simp
  have hr' : q * W ≤ sf.radius := by
    change q ^ (n + 1) * w ≤ sf.radius at hr
    rwa [he] at hr
  refine ⟨a, sf.function, sf.center, sf.smooth, sf.initial_value, sf.initial_derivative,
    sf.second_bound, ?_, ⟨sf.offset, sf.radius, sf.radius_pos, sf.local_polynomial⟩, ?_⟩
  · intro u
    have hb := sf.third_bound u
    have hc : 20 * q * K ≤ sf.radius := by
      nlinarith only [hr', hWbound, hq]
    exact hb.trans ((div_le_one sf.radius_pos).mpr hc)
  · change 4 * q ^ (n + 1) * w ≤ |(execute (oracle sf.function) (algorithm a)).fst - sf.center| at hdist
    have hge : 4 < 4 * q * W := by
      dsimp [W]
      have hcancel : q * (1 / q) = 1 := by field_simp
      nlinarith [mul_pos hq hK]
    have hbase : 4 * q ^ (n + 1) * w = 4 * q * W := by nlinarith only [he]
    linarith only [hdist, hbase, hge]

end
end OriginalWarmFiniteAdversary


open scoped ContDiff Topology

namespace OriginalWarmAdversaryRegularity

open OriginalWarmSaddleOracle OriginalWarmRefinementState

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
local instance : NormedSpace ℝ Space := inferInstance
local instance : ContinuousSMul ℝ Space := inferInstance

/-- A stationary point of an actual differentiable convex scalar function is a global
minimum, with no bound on its position required. -/
theorem scalar_minimum (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ Set.univ f) (a : ℝ) (ha : deriv f a = 0) :
    ∀ u, f a ≤ f u := by
  intro u
  rcases lt_trichotomy a u with h | h | h
  · have hs := hc.deriv_le_slope (Set.mem_univ a) (Set.mem_univ u) h (hf a)
    rw [ha, slope_def_field] at hs
    have hh := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    linarith
  · rw [h]
  · have hs := hc.slope_le_deriv (Set.mem_univ u) (Set.mem_univ a) h (hf a)
    rw [ha, slope_def_field] at hs
    have hh := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    linarith

theorem scalar_convex (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hsecond : ∀ u, |iteratedDeriv 2 f u - 1| ≤ 1 / 2) :
    ConvexOn ℝ Set.univ f := by
  apply convexOn_univ_of_deriv2_nonneg (hf.differentiable (by decide))
    (by simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by decide))
  intro u
  have hh := (abs_le.mp (hsecond u)).1
  change 0 ≤ deriv (deriv f) u
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using (show 0 ≤ iteratedDeriv 2 f u by linarith)

theorem scalar_gradient_lipschitz (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hsecond : ∀ u, |iteratedDeriv 2 f u - 1| ≤ 1 / 2) :
    LipschitzWith 2 (deriv f) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (by simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by decide))
  intro u
  have hh := abs_le.mp (hsecond u)
  have hb : |iteratedDeriv 2 f u| ≤ 2 := (abs_le.mpr (by constructor <;> linarith))
  have hb' : ‖deriv (deriv f) u‖ ≤ (2 : ℝ) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs] using hb
  exact_mod_cast hb'

theorem scalar_hessian_lipschitz (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hthird : ∀ u, |iteratedDeriv 3 f u| ≤ 1) :
    LipschitzWith 1 (iteratedDeriv 2 f) := by
  apply lipschitzWith_of_nnnorm_deriv_le (hf.differentiable_iteratedDeriv 2 (by decide))
  intro u
  have hb : ‖deriv (iteratedDeriv 2 f) u‖ ≤ (1 : ℝ) := by
    simpa only [iteratedDeriv_succ, Real.norm_eq_abs] using hthird u
  exact_mod_cast hb

theorem norm_squared (z : Space) : ‖z‖ ^ 2 = z.fst ^ 2 + z.snd ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using WithLp.prod_norm_sq_eq_of_L2 z

theorem actual_joint_gradient_lipschitz (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hsecond : ∀ u, |iteratedDeriv 2 f u - 1| ≤ 1 / 2) :
    LipschitzWith 2 (gradient (saddle f)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hg := scalar_gradient_lipschitz f hf hsecond
  have hb := hg.norm_sub_le z.fst w.fst
  have hb2 := mul_self_le_mul_self (norm_nonneg _) hb
  have he := norm_squared (gradient (saddle f) z - gradient (saddle f) w)
  have hgr := actual_gradient f (hf.of_le (by decide))
  rw [(hgr z).gradient, (hgr w).gradient] at he
  have he' : ‖gradient (saddle f) z - gradient (saddle f) w‖ ^ 2 =
      (deriv f z.fst - deriv f w.fst) ^ 2 + (z.snd - w.snd) ^ 2 := by
    rw [(hgr z).gradient, (hgr w).gradient]
    convert! he using 1 <;> simp only [point, WithLp.sub_fst, WithLp.sub_snd,
      WithLp.toLp_fst, WithLp.toLp_snd] <;> ring
  have hn := norm_squared (z - w)
  simp only [WithLp.sub_fst, WithLp.sub_snd] at hn
  norm_num only [NNReal.coe_ofNat, Real.norm_eq_abs] at hb2
  have hb2' : (deriv f z.fst - deriv f w.fst) ^ 2 ≤ 4 * (z.fst - w.fst) ^ 2 := by
    nlinarith only [hb2, sq_abs (deriv f z.fst - deriv f w.fst), sq_abs (z.fst - w.fst)]
  change ‖gradient (saddle f) z - gradient (saddle f) w‖ ≤ 2 * ‖z - w‖
  nlinarith only [hb2', he', hn, norm_nonneg (gradient (saddle f) z - gradient (saddle f) w), norm_nonneg (z - w),
    sq_nonneg (z.snd - w.snd)]

theorem diagonal_difference_bound (a b : ℝ) : ‖diagonal a - diagonal b‖ ≤ |a - b| := by
  refine (diagonal a - diagonal b).opNorm_le_bound (abs_nonneg _) ?_
  intro z
  have he : (diagonal a - diagonal b) z = point ((a - b) * z.fst) 0 := by
    apply (WithLp.ext_iff 2).mpr
    change (a * z.fst - b * z.fst, -z.snd - -z.snd) = ((a - b) * z.fst, 0)
    congr 1 <;> ring
  rw [he]
  change ‖WithLp.toLp 2 (((a - b) * z.fst), (0 : ℝ))‖ ≤ _
  rw [WithLp.norm_toLp_fst]
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (WithLp.norm_fst_le ℝ z) (abs_nonneg _)

theorem actual_joint_hessian_lipschitz (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hthird : ∀ u, |iteratedDeriv 3 f u| ≤ 1) :
    LipschitzWith 1 (fderiv ℝ (gradient (saddle f))) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [actual_hessian f (hf.of_le (by decide)) z, actual_hessian f (hf.of_le (by decide)) w]
  have hs := (scalar_hessian_lipschitz f hf hthird).norm_sub_le z.fst w.fst
  simp only [NNReal.coe_one, one_mul, Real.norm_eq_abs] at hs
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  exact (diagonal_difference_bound _ _).trans (hs.trans (by
    simpa only [WithLp.sub_fst, Real.norm_eq_abs, one_mul] using WithLp.norm_fst_le ℝ (z - w)))


theorem actual_joint_smooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (saddle f) := by
  change ContDiff ℝ ∞ (fun z : Space => f ((WithLp.fstL 2 ℝ ℝ ℝ) z) -
    ((WithLp.sndL 2 ℝ ℝ ℝ) z) ^ 2 / 2)
  fun_prop

theorem actual_dual_strong_concavity (f : ℝ → ℝ) (u : ℝ) :
    StrongConvexOn (Set.univ : Set ℝ) 1 (fun y => -saddle f (point u y)) := by
  apply strongConvexOn_iff_convex.mpr
  have he : (fun y : ℝ => -saddle f (point u y) - (1 : ℝ) / 2 * ‖y‖ ^ 2) =
      fun _ => -f u := by
    funext y
    change -(f u - y ^ 2 / 2) - (1 : ℝ) / 2 * ‖y‖ ^ 2 = -f u
    rw [Real.norm_eq_abs, sq_abs]
    ring
  rw [he]
  exact convexOn_const _ convex_univ

def proximal (f : ℝ → ℝ) (u : ℝ) := f u + 2 * u ^ 2

theorem proximal_deriv (f : ℝ → ℝ) (hf : Differentiable ℝ f) (u : ℝ) :
    deriv (proximal f) u = deriv f u + 4 * u := by
  apply HasDerivAt.deriv
  convert! ((hf u).hasDerivAt.add (((hasDerivAt_id u).pow 2).const_mul 2)) using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

theorem proximal_second (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (u : ℝ) :
    deriv (deriv (proximal f)) u = iteratedDeriv 2 f u + 4 := by
  have he : deriv (proximal f) = fun v => deriv f v + 4 * v :=
    funext (proximal_deriv f (hf.differentiable (by decide)))
  rw [he]
  have hfd : Differentiable ℝ (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.differentiable_iteratedDeriv 1 (by decide)
  have hd := (hfd u).hasDerivAt.add ((hasDerivAt_id u).const_mul 4)
  convert! hd.deriv using 1 <;> simp only [iteratedDeriv_succ, iteratedDeriv_zero, id_eq] <;> ring

theorem actual_proximal_minimum (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hsecond : ∀ u, |iteratedDeriv 2 f u - 1| ≤ 1 / 2)
    (m b w : ℝ) (hw : 0 < w)
    (hlocal : ∀ u, |u - m| < w → f u = polynomial m b u) :
    (∀ u, proximal f m ≤ proximal f u) ∧
    (∀ z, (∀ u, proximal f z ≤ proximal f u) → z = m) := by
  have hd := hf.differentiable (by decide)
  have hp : Differentiable ℝ (proximal f) := by unfold proximal; fun_prop
  have hstrict : StrictConvexOn ℝ Set.univ (proximal f) := by
    apply strictConvexOn_of_deriv2_pos' convex_univ hp.continuous.continuousOn
    intro u _
    change 0 < deriv (deriv (proximal f)) u
    rw [proximal_second f hf]
    have hh := (abs_le.mp (hsecond u)).1
    linarith
  have hgerm : f =ᶠ[𝓝 m] polynomial m b := by
    have hn : ∀ᶠ u : ℝ in 𝓝 m, |u - m| < w :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hw)
    filter_upwards [hn] with u hu
    exact hlocal u hu
  have hzero : deriv (proximal f) m = 0 := by
    rw [proximal_deriv f hd, hgerm.deriv_eq, polynomial_deriv]
    ring
  have hm := scalar_minimum (proximal f) hp hstrict.convexOn m hzero
  refine ⟨hm, ?_⟩
  intro z hz
  exact hstrict.eq_of_isMinOn (fun u _ => hz u) (fun u _ => hm u)
    (Set.mem_univ z) (Set.mem_univ m)

theorem actual_phi (f : ℝ → ℝ) (u : ℝ) :
    sSup (Set.range (fun y => saddle f (point u y))) = f u := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨0, ?_⟩, ?_⟩
  · change f u - 0 ^ 2 / 2 = f u
    ring
  · rintro _ ⟨y, rfl⟩
    change f u - y ^ 2 / 2 ≤ f u
    nlinarith only [sq_nonneg y]

end
end OriginalWarmAdversaryRegularity


open scoped ContDiff Topology

namespace OriginalWarmUniformDeterministicObstruction

open OriginalWarmSaddleOracle OriginalWarmRefinementState OriginalWarmResistingProgram
  OriginalWarmFiniteAdversary OriginalWarmAdversaryRegularity

noncomputable section
local instance : NormedSpace ℝ Space := inferInstance
local instance : ContinuousSMul ℝ Space := inferInstance

/-- The actual maximized primal value, with no supplied value-function hypothesis. -/
def phi (f : ℝ → ℝ) (u : ℝ) := sSup (Set.range (fun y => saddle f (point u y)))

/-- The original proximal saddle objective at the arbitrary center x=0 and L=2. -/
def proximalSaddle (f : ℝ → ℝ) (z : Space) := saddle f z + 2 * z.fst ^ 2

theorem actual_initial_gap_zero (f : ℝ → ℝ) (a : ℝ)
    (ha : f a = 0) (hmin : ∀ u, f a ≤ f u) :
    phi f a = 0 ∧ sInf (Set.range (phi f)) = 0 ∧
      phi f a - sInf (Set.range (phi f)) = 0 := by
  have hphi : phi f = f := funext (actual_phi f)
  rw [hphi]
  have hinf : sInf (Set.range f) = 0 := by
    apply IsLeast.csInf_eq
    refine ⟨⟨a, ha⟩, ?_⟩
    rintro _ ⟨u, rfl⟩
    simpa only [ha] using hmin u
  simp only [hinf, ha, sub_self, and_self]

/-- A genuine all-deterministic-algorithms obstruction to a finite budget depending
only on (L,mu,rho,Delta,Ry,D,tau)=(2,1,1,1,0,1,1). It does not impose any bound on
or hide any logarithm in the distance from the arbitrary center 0 to the public initial
point a. It does not make a randomized lower-bound claim. -/
theorem no_uniform_finite_deterministic_saddle_budget (n : ℕ)
    (algorithm : ℝ → Program Space Answer Space n) :
    ∃ (a : ℝ) (f : ℝ → ℝ) (m : ℝ),
      ContDiff ℝ 2 (saddle f) ∧
      LipschitzWith 2 (gradient (saddle f)) ∧
      LipschitzWith 1 (fderiv ℝ (gradient (saddle f))) ∧
      (∀ u : ℝ, StrongConvexOn (Set.univ : Set ℝ) 1
        (fun y => -saddle f (point u y))) ∧
      (∀ u : ℝ, saddle f (point u 0) = phi f u ∧
        ∀ y : ℝ, saddle f (point u y) ≤ saddle f (point u 0)) ∧
      phi f a = 0 ∧ sInf (Set.range (phi f)) = 0 ∧
      phi f a - sInf (Set.range (phi f)) ≤ 1 ∧
      (∀ y : ℝ, proximalSaddle f (point m y) ≤ proximalSaddle f (point m 0)) ∧
      (∀ u : ℝ, proximalSaddle f (point m 0) ≤ proximalSaddle f (point u 0)) ∧
      (∀ z : ℝ, (∀ u : ℝ, proximalSaddle f (point z 0) ≤ proximalSaddle f (point u 0)) → z = m) ∧
      ‖(0 : ℝ) - 0‖ ≤ 1 ∧
      1 < ‖execute (oracle f) (algorithm a) - point m 0‖ := by
  obtain ⟨a, f, m, hf, hfa, hda, hsecond, hthird, ⟨b, w, hw, hlocal⟩, hfail⟩ :=
    finite_exact_bundle_adversary n algorithm
  have hmin := scalar_minimum f (hf.differentiable (by decide))
    (scalar_convex f hf hsecond) a hda
  have hgap := actual_initial_gap_zero f a hfa hmin
  have hprox := actual_proximal_minimum f hf hsecond m b w hw hlocal
  refine ⟨a, f, m, (actual_joint_smooth f hf).of_le (by decide),
    actual_joint_gradient_lipschitz f hf hsecond,
    actual_joint_hessian_lipschitz f hf hthird,
    actual_dual_strong_concavity f, ?_, hgap.1, hgap.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    constructor
    · change f u - 0 ^ 2 / 2 = phi f u
      rw [show phi f u = f u from actual_phi f u]
      ring
    · intro y
      change f u - y ^ 2 / 2 ≤ f u - 0 ^ 2 / 2
      nlinarith only [sq_nonneg y]
  · rw [hgap.2.2]
    norm_num
  · intro y
    change f m - y ^ 2 / 2 + 2 * m ^ 2 ≤ f m - 0 ^ 2 / 2 + 2 * m ^ 2
    nlinarith only [sq_nonneg y]
  · intro u
    simpa only [proximalSaddle, saddle, point, WithLp.toLp_fst, WithLp.toLp_snd,
      pow_two, zero_mul, zero_div, sub_zero, proximal] using hprox.1 u
  · intro z hz
    apply hprox.2 z
    intro u
    simpa only [proximalSaddle, saddle, point, WithLp.toLp_fst, WithLp.toLp_snd,
      pow_two, zero_mul, zero_div, sub_zero, proximal] using hz u
  · norm_num
  · have hb := WithLp.norm_fst_le ℝ (execute (oracle f) (algorithm a) - point m 0)
    have hb' : |(execute (oracle f) (algorithm a)).fst - m| ≤
        ‖execute (oracle f) (algorithm a) - point m 0‖ := by
      simpa only [WithLp.sub_fst, point, WithLp.toLp_fst, Real.norm_eq_abs] using hb
    exact hfail.trans_le hb'

end
end OriginalWarmUniformDeterministicObstruction


namespace OriginalWarmBinaryAverage
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def Word : ℕ → Type
  | 0 => PUnit
  | n+1 => Bool × Word n

def average : (n : ℕ) → (Word n → ℝ) → ℝ
  | 0, f => f PUnit.unit
  | n+1, f => (average n (fun w => f (false,w)) + average n (fun w => f (true,w))) / 2

theorem average_const (n : ℕ) (c : ℝ) : average n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [average,ih]; ring

theorem average_add (n : ℕ) (f g : Word n → ℝ) :
    average n (fun w => f w + g w) = average n f + average n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [average,ih]; ring

theorem average_mul (n : ℕ) (c : ℝ) (f : Word n → ℝ) :
    average n (fun w => c * f w) = c * average n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [average,ih]; ring

theorem average_mono (n : ℕ) (f g : Word n → ℝ) (h : ∀ w, f w ≤ g w) :
    average n f ≤ average n g := by
  induction n with
  | zero => exact h PUnit.unit
  | succ n ih =>
      exact div_le_div_of_nonneg_right
        (add_le_add (ih _ _ (fun w => h (false,w))) (ih _ _ (fun w => h (true,w)))) (by norm_num)

theorem average_nonnegative (n : ℕ) (f : Word n → ℝ) (h : ∀ w, 0 ≤ f w) : 0 ≤ average n f := by
  have hh := average_mono n (fun _ => 0) f h
  rwa [average_const] at hh

theorem average_nat_succ (n : ℕ) (f : Word n → ℕ) :
    average n (fun w => (1 + f w : ℕ)) = 1 + average n (fun w => (f w : ℝ)) := by
  simp only [Nat.cast_add,Nat.cast_one]
  rw [average_add,average_const]

def probability (n : ℕ) (P : Word n → Prop) := average n (fun w => if P w then 1 else 0)

theorem probability_nonnegative (n : ℕ) (P : Word n → Prop) : 0 ≤ probability n P :=
  average_nonnegative n _ (fun w => by split_ifs <;> norm_num)

theorem probability_le_one (n : ℕ) (P : Word n → Prop) : probability n P ≤ 1 := by
  have h := average_mono n (fun w => if P w then 1 else 0) (fun _ => 1) (fun w => by split_ifs <;> norm_num)
  rwa [average_const] at h

/-- Finite Markov inequality, with no randomness or algorithmic independence
premise hidden in the averaging step. The word distribution is fixed in advance. -/
theorem probability_le_expected_cost (n : ℕ) (P : Word n → Prop)
    (cost : Word n → ℕ) (N : ℝ) (hN : 0 < N)
    (hcost : ∀ w, P w → N ≤ (cost w : ℝ)) :
    probability n P ≤ average n (fun w => (cost w : ℝ)) / N := by
  apply (le_div_iff₀ hN).mpr
  have h := average_mono n (fun w => N * (if P w then 1 else 0))
    (fun w => (cost w : ℝ)) (fun w => by
      by_cases hp : P w
      · simpa only [if_pos hp,mul_one] using hcost w hp
      · simp only [if_neg hp,mul_zero]
        positivity)
  rw [average_mul] at h
  unfold probability
  nlinarith only [h]

end
end OriginalWarmBinaryAverage


namespace OriginalWarmBinaryDisclosure
open OriginalWarmBinaryAverage OriginalWarmResistingProgram
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 3000000

structure Scheme (S Q Reply : Type*) where
  oracle : S → Q → Reply
  child : S → Bool → S
  near : S → Q → Prop
  disjoint : ∀ s q, ¬ (near (child s false) q ∧ near (child s true) q)

variable {S Q Reply : Type*}

def currentPoint {n : ℕ} : Program Q Reply Q n → Q
  | .pure v => v
  | .ask q _ => q

/-- The next bit is revealed only to decide the actual current probe. On a miss,
all further compact perturbations vanish at that probe, so the real algorithm can
consume its query. A terminal unqueried output is tested by the same procedure. -/
def probeCost (C : Scheme S Q Reply) : (m : ℕ) → {n : ℕ} →
    S → Program Q Reply Q n → Word m → ℕ
  | 0, _, _, _, _ => 0
  | m+1, _, s, p, (b,w) =>
      let t := C.child s b
      if C.near t (currentPoint p) then 1 + probeCost C m t p w
      else match p with
      | .pure _ => 1
      | .ask q next => 1 + probeCost C m t (next (C.oracle t q)) w

theorem probe_cost_le_depth (C : Scheme S Q Reply) (m : ℕ) {n : ℕ}
    (s : S) (p : Program Q Reply Q n) (w : Word m) : probeCost C m s p w ≤ m := by
  induction m generalizing n s with
  | zero => rfl
  | succ m ih =>
      rcases w with ⟨b,w⟩
      simp only [probeCost]
      split_ifs
      · have hh := ih (C.child s b) p w
        omega
      · cases p with
        | pure v =>
            change 1 ≤ m + 1
            omega
        | ask q next =>
            change 1 + probeCost C m (C.child s b) (next (C.oracle (C.child s b) q)) w ≤ m + 1
            have hh := ih (C.child s b) (next (C.oracle (C.child s b) q)) w
            omega

/-- At most one of the two next child intervals can contain a fixed probe. Thus
each actual query, and the final output test, discloses at most two bits in
expectation, even though a lucky probe may disclose many consecutive bits. -/
theorem expected_disclosures_le_twice_queries_plus_output
    (C : Scheme S Q Reply) (m : ℕ) {n : ℕ} (s : S) (p : Program Q Reply Q n) :
    average m (fun w => (probeCost C m s p w : ℝ)) ≤ 2 * ((n : ℝ) + 1) := by
  induction m generalizing n s with
  | zero => simp only [average,probeCost,Nat.cast_zero]; positivity
  | succ m ih =>
      cases p with
      | @pure n v =>
          have hf := ih (s := C.child s false) (p := (Program.pure v : Program Q Reply Q n))
          have ht := ih (s := C.child s true) (p := (Program.pure v : Program Q Reply Q n))
          have hd := C.disjoint s v
          by_cases h0 : C.near (C.child s false) v <;>
            by_cases h1 : C.near (C.child s true) v
          · exact (hd ⟨h0,h1⟩).elim
          · simp only [average,probeCost,currentPoint,if_pos h0,if_neg h1,average_nat_succ,average_const]
            nlinarith only [hf,(show (0 : ℝ) ≤ (n : ℝ) by positivity)]
          · simp only [average,probeCost,currentPoint,if_neg h0,if_pos h1,average_nat_succ,average_const]
            nlinarith only [ht,(show (0 : ℝ) ≤ (n : ℝ) by positivity)]
          · simp only [average,probeCost,currentPoint,if_neg h0,if_neg h1,average_const]
            nlinarith only [(show (0 : ℝ) ≤ (n : ℝ) by positivity)]
      | @ask n q next =>
          have hf := ih (s := C.child s false) (p := (Program.ask q next))
          have ht := ih (s := C.child s true) (p := (Program.ask q next))
          have hmf := ih (s := C.child s false) (p := next (C.oracle (C.child s false) q))
          have hmt := ih (s := C.child s true) (p := next (C.oracle (C.child s true) q))
          have hd := C.disjoint s q
          by_cases h0 : C.near (C.child s false) q <;>
            by_cases h1 : C.near (C.child s true) q
          · exact (hd ⟨h0,h1⟩).elim
          · simp only [average,probeCost,currentPoint,if_pos h0,if_neg h1,average_nat_succ]
            push_cast at hf ht ⊢
            nlinarith only [hf,hmt]
          · simp only [average,probeCost,currentPoint,if_neg h0,if_pos h1,average_nat_succ]
            push_cast at hf ht ⊢
            nlinarith only [ht,hmf]
          · simp only [average,probeCost,currentPoint,if_neg h0,if_neg h1,average_nat_succ]
            push_cast
            nlinarith only [hmf,hmt]

end
end OriginalWarmBinaryDisclosure


namespace OriginalWarmBinaryPhysical
open OriginalWarmCompactPotential OriginalWarmRefinementState OriginalWarmSaddleOracle
open OriginalWarmBinaryAverage OriginalWarmBinaryDisclosure OriginalWarmResistingProgram
noncomputable section
set_option maxHeartbeats 3000000

variable {q K a : ℝ} (hq : 0 < q) (hsmall : q ≤ 1/16) (hK : 0 ≤ K)
  (hcurv : 20*q*K ≤ 1/2)
  (hprofile : ∀ j : ℕ, j ≤ 3 → ∀ t : ℝ, |iteratedDeriv j potential t| ≤ K)

def child (s : State q K a) (b : Bool) : State q K a :=
  if b then refine hq hsmall hK hcurv hprofile s (s.center-1)
  else refine hq hsmall hK hcurv hprofile s (s.center+1)

theorem child_radius (s : State q K a) (b : Bool) :
    (child hq hsmall hK hcurv hprofile s b).radius = q * s.radius := by cases b <;> rfl

theorem child_center_false (s : State q K a) :
    (child hq hsmall hK hcurv hprofile s false).center = s.center - 4*q*s.radius := by
  change s.center + 4 * signChoice s.center (s.center+1) * q * s.radius = _
  have hs : signChoice s.center (s.center+1) = -1 := by unfold signChoice; rw [if_neg (by linarith)]
  rw [hs]
  ring

theorem child_center_true (s : State q K a) :
    (child hq hsmall hK hcurv hprofile s true).center = s.center + 4*q*s.radius := by
  change s.center + 4 * signChoice s.center (s.center-1) * q * s.radius = _
  have hs : signChoice s.center (s.center-1) = 1 := by unfold signChoice; rw [if_pos (by linarith)]
  rw [hs]
  ring

def near (s : State q K a) (z : Space) := |z.fst-s.center| < s.radius

theorem children_disjoint (s : State q K a) (z : Space) :
    ¬ (near (child hq hsmall hK hcurv hprofile s false) z ∧
      near (child hq hsmall hK hcurv hprofile s true) z) := by
  rintro ⟨hl,hr⟩
  unfold near at hl hr
  rw [child_center_false,child_radius] at hl
  rw [child_center_true,child_radius] at hr
  have h1 := (abs_lt.mp hl).2
  have h2 := (abs_lt.mp hr).1
  have hp := mul_pos hq s.radius_pos
  nlinarith only [h1,h2,hp]

def scheme : OriginalWarmBinaryDisclosure.Scheme (State q K a) Space Answer where
  oracle s := OriginalWarmSaddleOracle.oracle s.function
  child := child hq hsmall hK hcurv hprofile
  near := near
  disjoint := children_disjoint hq hsmall hK hcurv hprofile

/-- Each binary word defines an actual smooth fixed instance before any queries.
No child choice here observes an algorithm, its seed, or its transcript. -/
def family : (m : ℕ) → State q K a → Word m → State q K a
  | 0, s, _ => s
  | m+1, s, (b,w) => family m (child hq hsmall hK hcurv hprofile s b) w

theorem family_radius (m : ℕ) (s : State q K a) (w : Word m) :
    (family hq hsmall hK hcurv hprofile m s w).radius = q^m * s.radius := by
  induction m generalizing s with
  | zero => simp only [family,pow_zero,one_mul]
  | succ m ih =>
      rcases w with ⟨b,w⟩
      rw [family,ih,child_radius,pow_succ]
      ring

theorem family_center_inside (m : ℕ) (s : State q K a) (w : Word m) :
    |(family hq hsmall hK hcurv hprofile m s w).center-s.center| ≤ s.radius/2 := by
  induction m generalizing s with
  | zero => simp only [family,sub_self,abs_zero]; linarith only [s.radius_pos]
  | succ m ih =>
      rcases w with ⟨b,w⟩
      have hrec := ih (child hq hsmall hK hcurv hprofile s b) w
      have hprod : 0 < 4*q*s.radius := by have hw := s.radius_pos; positivity
      have hstep : |(child hq hsmall hK hcurv hprofile s b).center-s.center| = 4*q*s.radius := by
        cases b
        · rw [child_center_false]
          rw [show s.center-4*q*s.radius-s.center = -(4*q*s.radius) by ring,abs_neg,abs_of_pos hprod]
        · rw [child_center_true,add_sub_cancel_left,abs_of_pos hprod]
      have ht := abs_add_le
        ((family hq hsmall hK hcurv hprofile m (child hq hsmall hK hcurv hprofile s b) w).center-
          (child hq hsmall hK hcurv hprofile s b).center)
        ((child hq hsmall hK hcurv hprofile s b).center-s.center)
      rw [sub_add_sub_cancel,hstep] at ht
      rw [child_radius] at hrec
      change |(family hq hsmall hK hcurv hprofile m (child hq hsmall hK hcurv hprofile s b) w).center-s.center| ≤ _
      have hs := mul_le_mul_of_nonneg_right hsmall s.radius_pos.le
      nlinarith only [ht,hrec,hs,s.radius_pos]

end
end OriginalWarmBinaryPhysical


namespace OriginalWarmBinaryPhysical
open OriginalWarmCompactPotential OriginalWarmRefinementState OriginalWarmSaddleOracle
open OriginalWarmBinaryAverage OriginalWarmBinaryDisclosure OriginalWarmResistingProgram
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 3000000

variable {q K a : ℝ} (hq : 0 < q) (hsmall : q ≤ 1/16) (hK : 0 ≤ K)
  (hcurv : 20*q*K ≤ 1/2)
  (hprofile : ∀ j : ℕ, j ≤ 3 → ∀ t : ℝ, |iteratedDeriv j potential t| ≤ K)

theorem child_center_displacement (s : State q K a) (b : Bool) :
    |(child hq hsmall hK hcurv hprofile s b).center-s.center| = 4*q*s.radius := by
  have hp : 0 < 4*q*s.radius := by have hw := s.radius_pos; positivity
  cases b
  · rw [child_center_false]
    rw [show s.center-4*q*s.radius-s.center = -(4*q*s.radius) by ring,abs_neg,abs_of_pos hp]
  · rw [child_center_true,add_sub_cancel_left,abs_of_pos hp]

theorem outside_child (s : State q K a) (b : Bool) (u : ℝ)
    (hu : s.radius ≤ |u-s.center|) :
    (child hq hsmall hK hcurv hprofile s b).radius ≤
      |u-(child hq hsmall hK hcurv hprofile s b).center| := by
  have ht := abs_add_le (u-(child hq hsmall hK hcurv hprofile s b).center)
    ((child hq hsmall hK hcurv hprofile s b).center-s.center)
  rw [sub_add_sub_cancel,child_center_displacement] at ht
  rw [child_radius]
  have hs := mul_le_mul_of_nonneg_right hsmall s.radius_pos.le
  nlinarith only [ht,hu,hs,s.radius_pos]

theorem child_function_germ_outside (s : State q K a) (b : Bool) (u : ℝ)
    (hu : s.radius ≤ |u-s.center|) :
    (child hq hsmall hK hcurv hprofile s b).function =ᶠ[𝓝 u] s.function := by
  cases b
  · exact refined_function_germ_outside s (s.center+1) u hu
  · exact refined_function_germ_outside s (s.center-1) u hu

/-- Literal equality of the full actual joint value/gradient/Hessian bundle for
every unobserved compact descendant, at an arbitrary query outside its parent. -/
theorem family_oracle_outside (m : ℕ) (s : State q K a) (w : Word m) (z : Space)
    (hz : s.radius ≤ |z.fst-s.center|) :
    oracle (family hq hsmall hK hcurv hprofile m s w).function z = oracle s.function z := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
      rcases w with ⟨b,w⟩
      rw [family,ih _ _ (outside_child hq hsmall hK hcurv hprofile s b z.fst hz)]
      exact oracle_eq_of_scalar_germ _ _ z (child_function_germ_outside hq hsmall hK hcurv hprofile s b z.fst hz)

theorem far_output_on_miss (m : ℕ) (s : State q K a) (w : Word m) (z : Space)
    (hbig : 2 < (family hq hsmall hK hcurv hprofile m s w).radius)
    (hmiss : ¬ near s z) :
    1 < |z.fst-(family hq hsmall hK hcurv hprofile m s w).center| := by
  have hq1 : q ≤ 1 := by linarith only [hsmall]
  have hpow : q^m ≤ 1 := pow_le_one₀ hq.le hq1
  have hr : (family hq hsmall hK hcurv hprofile m s w).radius ≤ s.radius := by
    rw [family_radius]
    exact mul_le_of_le_one_left s.radius_pos.le hpow
  have hcenter := family_center_inside hq hsmall hK hcurv hprofile m s w
  have ht := abs_add_le (z.fst-(family hq hsmall hK hcurv hprofile m s w).center)
    ((family hq hsmall hK hcurv hprofile m s w).center-s.center)
  rw [sub_add_sub_cancel] at ht
  have haway : s.radius ≤ |z.fst-s.center| := le_of_not_gt hmiss
  nlinarith only [hbig,hr,hcenter,ht,haway]

/-- The fixed binary-word instance exactly replays every query on each miss
branch. If its returned (possibly unqueried) point is accurate, all bits must
have been disclosed by the augmented probe process. -/
theorem actual_success_requires_full_disclosure (m : ℕ) {n : ℕ}
    (s : State q K a) (w : Word m) (p : Program Space Answer Space n)
    (hbig : 2 < (family hq hsmall hK hcurv hprofile m s w).radius)
    (hsuccess : |(OriginalWarmResistingProgram.execute
      (oracle (family hq hsmall hK hcurv hprofile m s w).function) p).fst-
      (family hq hsmall hK hcurv hprofile m s w).center| ≤ 1) :
    probeCost (scheme hq hsmall hK hcurv hprofile) m s p w = m := by
  induction m generalizing n s with
  | zero => rfl
  | succ m ih =>
      rcases w with ⟨b,w⟩
      let t := child hq hsmall hK hcurv hprofile s b
      by_cases hnear : near t (currentPoint p)
      · change (if near t (currentPoint p) then
          1 + probeCost (scheme hq hsmall hK hcurv hprofile) m t p w else _) = m+1
        rw [if_pos hnear,ih t w p hbig hsuccess]
        omega
      · cases p with
        | pure z =>
            have hf := far_output_on_miss hq hsmall hK hcurv hprofile m t w z hbig hnear
            change |z.fst-(family hq hsmall hK hcurv hprofile m t w).center| ≤ 1 at hsuccess
            linarith only [hf,hsuccess]
        | ask z next =>
            change ¬ near t z at hnear
            have hz : t.radius ≤ |z.fst-t.center| := le_of_not_gt hnear
            have horacle := family_oracle_outside hq hsmall hK hcurv hprofile m t w z hz
            have hnext := hsuccess
            change |(OriginalWarmResistingProgram.execute
              (oracle (family hq hsmall hK hcurv hprofile m t w).function) (.ask z next)).fst-
              (family hq hsmall hK hcurv hprofile m t w).center| ≤ 1 at hnext
            simp only [OriginalWarmResistingProgram.execute,horacle] at hnext
            change (if near t z then _ else
              1 + probeCost (scheme hq hsmall hK hcurv hprofile) m t (next (oracle t.function z)) w) = m+1
            rw [if_neg hnear,ih t w (next (oracle t.function z)) hbig hnext]
            omega

end
end OriginalWarmBinaryPhysical


namespace OriginalWarmBinaryPhysical
open OriginalWarmCompactPotential OriginalWarmRefinementState OriginalWarmSaddleOracle
open OriginalWarmBinaryAverage OriginalWarmBinaryDisclosure OriginalWarmResistingProgram
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 3000000
local instance : NormedSpace ℝ Space := inferInstance
local instance : ContinuousSMul ℝ Space := inferInstance

variable {q K a : ℝ} (hq : 0 < q) (hsmall : q ≤ 1/16) (hK : 0 ≤ K)
  (hcurv : 20*q*K ≤ 1/2)
  (hprofile : ∀ j : ℕ, j ≤ 3 → ∀ t : ℝ, |iteratedDeriv j potential t| ≤ K)

def jointSuccess (m : ℕ) (s : State q K a) {n : ℕ} (p : Program Space Answer Space n)
    (w : Word m) : Prop :=
  ‖OriginalWarmResistingProgram.execute
      (oracle (family hq hsmall hK hcurv hprofile m s w).function) p -
    point (family hq hsmall hK hcurv hprofile m s w).center 0‖ ≤ 1

/-- A finite, fixed, algorithm-independent family defeats every deterministic
query tree on average. This already includes arbitrary exact full-bundle replies,
early stopping and an unqueried output; the seed average is taken separately. -/
theorem fixed_family_average_success_le_one_third
    (m n : ℕ) (hm : 6 * (n+1) ≤ m) (s : State q K a)
    (hbig : ∀ w : Word m, 2 < (family hq hsmall hK hcurv hprofile m s w).radius)
    (p : Program Space Answer Space n) :
    probability m (jointSuccess hq hsmall hK hcurv hprofile m s p) ≤ 1/3 := by
  let C : OriginalWarmBinaryDisclosure.Scheme (State q K a) Space Answer := scheme hq hsmall hK hcurv hprofile
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hs (w : Word m) (hw : jointSuccess hq hsmall hK hcurv hprofile m s p w) :
      (m : ℝ) ≤ (probeCost C m s p w : ℝ) := by
    let sf := family hq hsmall hK hcurv hprofile m s w
    let out := OriginalWarmResistingProgram.execute (oracle sf.function) p
    have hf := WithLp.norm_fst_le ℝ (out-point sf.center 0)
    have hscalar : |out.fst-sf.center| ≤ 1 := by
      have hh : |out.fst-sf.center| ≤ ‖out-point sf.center 0‖ := by
        simpa only [WithLp.sub_fst,point,WithLp.toLp_fst,Real.norm_eq_abs] using hf
      exact hh.trans hw
    have he := actual_success_requires_full_disclosure hq hsmall hK hcurv hprofile m s w p (hbig w) hscalar
    change probeCost C m s p w = m at he
    exact_mod_cast he.ge
  have hmarkov := probability_le_expected_cost m
    (jointSuccess hq hsmall hK hcurv hprofile m s p) (fun w => probeCost C m s p w) m hmpos hs
  have hexpect := expected_disclosures_le_twice_queries_plus_output C m s p
  have hmreal : 6 * ((n : ℝ)+1) ≤ (m : ℝ) := by exact_mod_cast hm
  have hratio : average m (fun w => (probeCost C m s p w : ℝ)) / (m : ℝ) ≤ 1/3 := by
    apply (div_le_iff₀ hmpos).mpr
    nlinarith only [hexpect,hmreal]
  exact hmarkov.trans hratio

end
end OriginalWarmBinaryPhysical


namespace OriginalWarmBinarySeedAverage
open MeasureTheory OriginalWarmBinaryAverage
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 3000000

variable {Seed : Type*} [MeasurableSpace Seed] (mu : Measure Seed)

theorem integral_average (m : ℕ) (f : Word m → Seed → ℝ)
    (hf : ∀ w, Integrable (f w) mu) :
    Integrable (fun s => average m (fun w => f w s)) mu ∧
    (∫ s, average m (fun w => f w s) ∂mu) = average m (fun w => ∫ s, f w s ∂mu) := by
  induction m with
  | zero => exact ⟨hf PUnit.unit,rfl⟩
  | succ m ih =>
      have hl := ih (fun w => f (false,w)) (fun w => hf (false,w))
      have hr := ih (fun w => f (true,w)) (fun w => hf (true,w))
      refine ⟨(hl.1.add hr.1).div_const 2,?_⟩
      change (∫ s, (average m (fun w => f (false,w) s) + average m (fun w => f (true,w) s))/2 ∂mu) = _
      rw [integral_div,integral_add hl.1 hr.1,hl.2,hr.2]
      rfl

theorem strict_lower_average (m : ℕ) (f : Word m → ℝ) (c : ℝ) (h : ∀ w, c < f w) :
    c < average m f := by
  induction m with
  | zero => exact h PUnit.unit
  | succ m ih =>
      have hl := ih (fun w => f (false,w)) (fun w => h (false,w))
      have hr := ih (fun w => f (true,w)) (fun w => h (true,w))
      change c < (average m (fun w => f (false,w)) + average m (fun w => f (true,w)))/2
      linarith only [hl,hr]

/-- Finite averaging commutes with the arbitrary independent algorithmic seed.
It selects one fixed word before the realized seed; there is no per-seed choice
of a hard instance and no restriction to finitely many seeds. -/
theorem exists_fixed_word_with_small_seed_success [IsProbabilityMeasure mu]
    (m : ℕ) (P : Word m → Seed → Prop) (c : ℝ)
    (hP : ∀ w, MeasurableSet {s | P w s})
    (hbound : ∀ s, probability m (fun w => P w s) ≤ c) :
    ∃ w : Word m, mu.real {s | P w s} ≤ c := by
  let f : Word m → Seed → ℝ := fun w s => if P w s then 1 else 0
  have hf (w : Word m) : Integrable (f w) mu := by
    convert! (integrable_const (μ := mu) (1 : ℝ)).indicator (hP w) using 1
  have hInt (w : Word m) : (∫ s, f w s ∂mu) = mu.real {s | P w s} := by
    simpa only [f,Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using
      (integral_indicator_one (μ := mu) (hP w))
  have havg := integral_average mu m f hf
  have hi := integral_mono havg.1 (integrable_const c) hbound
  have hc : (∫ _s : Seed, c ∂mu) = c := by simp
  rw [havg.2,hc] at hi
  have heq : average m (fun w => ∫ s, f w s ∂mu) = average m (fun w => mu.real {s | P w s}) :=
    congrArg (average m) (funext hInt)
  rw [heq] at hi
  by_contra hn
  have hall : ∀ w : Word m, c < mu.real {s | P w s} := by
    intro w
    exact lt_of_not_ge (fun hw => hn ⟨w,hw⟩)
  exact (not_lt_of_ge hi) (strict_lower_average m _ c hall)

end
end OriginalWarmBinarySeedAverage


open scoped ContDiff Topology

namespace OriginalWarmRandomizedUniformObstruction
open MeasureTheory OriginalWarmCompactPotential OriginalWarmRefinementState OriginalWarmSaddleOracle
open OriginalWarmResistingProgram OriginalWarmBinaryAverage OriginalWarmBinaryPhysical
open OriginalWarmAdversaryRegularity OriginalWarmUniformDeterministicObstruction

noncomputable section
local instance : NormedSpace ℝ Space := inferInstance
local instance : ContinuousSMul ℝ Space := inferInstance
set_option maxHeartbeats 3000000

structure Legal (a : ℝ) (f : ℝ → ℝ) (m : ℝ) : Prop where
  smooth : ContDiff ℝ 2 (saddle f)
  gradient_lipschitz : LipschitzWith 2 (gradient (saddle f))
  hessian_lipschitz : LipschitzWith 1 (fderiv ℝ (gradient (saddle f)))
  dual_strong_concavity : ∀ u : ℝ, StrongConvexOn (Set.univ : Set ℝ) 1 (fun y => -saddle f (point u y))
  exact_initial_dual : ∀ u : ℝ, saddle f (point u 0) = phi f u ∧
    ∀ y : ℝ, saddle f (point u y) ≤ saddle f (point u 0)
  initial_value : phi f a = 0
  infimum_value : sInf (Set.range (phi f)) = 0
  initial_gap : phi f a - sInf (Set.range (phi f)) ≤ 1
  proximal_y_max : ∀ y : ℝ, proximalSaddle f (point m y) ≤ proximalSaddle f (point m 0)
  proximal_u_min : ∀ u : ℝ, proximalSaddle f (point m 0) ≤ proximalSaddle f (point u 0)
  proximal_u_unique : ∀ z : ℝ,
    (∀ u : ℝ, proximalSaddle f (point z 0) ≤ proximalSaddle f (point u 0)) → z = m

def Success (f : ℝ → ℝ) (m : ℝ) {n : ℕ} (p : Program Space Answer Space n) : Prop :=
  ‖OriginalWarmResistingProgram.execute (oracle f) p - point m 0‖ ≤ 1

theorem state_is_legal {q K a : ℝ} (s : State q K a)
    (hthird : ∀ u : ℝ, |iteratedDeriv 3 s.function u| ≤ 1) : Legal a s.function s.center := by
  have hmin := scalar_minimum s.function (s.smooth.differentiable (by simp))
    (scalar_convex s.function s.smooth s.second_bound) a s.initial_derivative
  have hgap := actual_initial_gap_zero s.function a s.initial_value hmin
  have hprox := actual_proximal_minimum s.function s.smooth s.second_bound s.center s.offset
    s.radius s.radius_pos s.local_polynomial
  refine ⟨(actual_joint_smooth s.function s.smooth).of_le (by decide),
    actual_joint_gradient_lipschitz s.function s.smooth s.second_bound,
    actual_joint_hessian_lipschitz s.function s.smooth hthird,
    actual_dual_strong_concavity s.function, ?_, hgap.1,hgap.2.1,?_,?_,?_,?_⟩
  · intro u
    constructor
    · change s.function u - 0 ^ 2 / 2 = phi s.function u
      rw [show phi s.function u = s.function u from actual_phi s.function u]
      ring
    · intro y
      change s.function u-y^2/2 ≤ s.function u-0^2/2
      nlinarith only [sq_nonneg y]
  · rw [hgap.2.2]
    norm_num
  · intro y
    change s.function s.center-y^2/2+2*s.center^2 ≤ s.function s.center-0^2/2+2*s.center^2
    nlinarith only [sq_nonneg y]
  · intro u
    simpa only [proximalSaddle,saddle,point,WithLp.toLp_fst,WithLp.toLp_snd,
      pow_two,zero_mul,zero_div,sub_zero,proximal] using hprox.1 u
  · intro z hz
    apply hprox.2 z
    intro u
    simpa only [proximalSaddle,saddle,point,WithLp.toLp_fst,WithLp.toLp_snd,
      pow_two,zero_mul,zero_div,sub_zero,proximal] using hz u

/-- One finite binary distribution is fixed from the budget before any algorithm
or random seed. Its public initial point is shared by all members and is supplied
to the algorithm. Every member satisfies the same original numerical parameters
(L,mu,rho,Delta,Ry,D,tau)=(2,1,1,1,0,1,1). -/
theorem shared_globally_legal_finite_family (n : ℕ) :
    ∃ (a : ℝ) (fs : Word (6*(n+1)) → ℝ → ℝ) (centers : Word (6*(n+1)) → ℝ),
      (∀ w, Legal a (fs w) (centers w)) ∧
      (∀ p : Program Space Answer Space n,
        probability (6*(n+1)) (fun w => Success (fs w) (centers w) p) ≤ 1/3) := by
  obtain ⟨K,hK1,hprofile⟩ := potential_global_derivative_bounds
  have hK : 0 < K := by linarith only [hK1]
  let q : ℝ := 1/(80*(K+1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hsmall : q ≤ 1/16 := by
    dsimp [q]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hK1]
  have hcurv : 20*q*K ≤ 1/2 := by
    dsimp [q]
    have he : 20*(1/(80*(K+1)))*K = K/(4*(K+1)) := by field_simp; ring
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hK1]
  let M : ℕ := 6*(n+1)
  let W : ℝ := 3+20*q*K+1/q
  have hW : 0 < W := by dsimp [W]; positivity
  have hWbig : 2 < W := by
    have hi := one_div_pos.mpr hq
    have hh : 0 ≤ 20*q*K := by positivity
    dsimp [W]
    linarith only [hi,hh]
  have hWthird : 20*q*K ≤ W := by dsimp [W]; have hi := one_div_pos.mpr hq; linarith only [hi]
  let width : ℝ := W/q^M
  have hwidth : 0 < width := by dsimp [width]; positivity
  let a : ℝ := -20*width
  let s0 : State q K a := initial q K width hq.le hK.le hwidth
  let states : Word M → State q K a := family hq hsmall hK.le hcurv hprofile M s0
  have hR (w : Word M) : (states w).radius = W := by
    have hh := family_radius hq hsmall hK.le hcurv hprofile M s0 w
    change (states w).radius = q^M*width at hh
    rw [hh]
    dsimp [width]
    field_simp
  have hlegal (w : Word M) : Legal a (states w).function (states w).center := by
    apply state_is_legal
    intro u
    have hb := (states w).third_bound u
    exact hb.trans ((div_le_one (states w).radius_pos).mpr (by rw [hR]; exact hWthird))
  refine ⟨a,(fun w => (states w).function),(fun w => (states w).center),hlegal,?_⟩
  intro p
  exact fixed_family_average_success_le_one_third hq hsmall hK.le hcurv hprofile M n le_rfl s0
    (fun w => by rw [← hR w] at hWbig; exact hWbig) p

/-- A randomized solver's seed may have any probability law and is independent
of the fixed family. The hard word is selected by averaging the whole seed law,
not after observing its realization. No finite uniform original-O2 budget exists
at the fixed displayed numeric tuple under that parameter-uniform reading. -/
theorem no_uniform_finite_randomized_saddle_budget
    {Seed : Type*} [MeasurableSpace Seed] (muSeed : Measure Seed) [IsProbabilityMeasure muSeed]
    (n : ℕ) (algorithm : ℝ → Seed → Program Space Answer Space n)
    (hmeas : ∀ (a : ℝ) (f : ℝ → ℝ) (m : ℝ), Legal a f m →
      MeasurableSet {seed | Success f m (algorithm a seed)}) :
    ∃ (a : ℝ) (f : ℝ → ℝ) (m : ℝ), Legal a f m ∧
      muSeed.real {seed | Success f m (algorithm a seed)} ≤ 1/3 := by
  obtain ⟨a,fs,centers,hlegal,haverage⟩ := shared_globally_legal_finite_family n
  obtain ⟨w,hw⟩ := OriginalWarmBinarySeedAverage.exists_fixed_word_with_small_seed_success muSeed
    (6*(n+1)) (fun w seed => Success (fs w) (centers w) (algorithm a seed)) (1/3)
    (fun w => hmeas a (fs w) (centers w) (hlegal w)) (fun seed => haverage (algorithm a seed))
  exact ⟨a,fs w,centers w,hlegal w,hw⟩

end
end OriginalWarmRandomizedUniformObstruction
end PaperAudit.WarmUniformCounterexample
