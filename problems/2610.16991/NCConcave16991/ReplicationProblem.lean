import NCConcave16991.Replication
import NCConcave16991.ProblemAnalysis
import NCConcave16991.MoreauParameter
import NCConcave16991.TheoremStatements

/-! # Balanced replication of actual admissible finite-sum Problems -/

noncomputable section

open Set
open scoped BigOperators InnerProductSpace

namespace NCConcave16991.Replication

abbrev sourceParameters (p : ProblemParameters) (s : ℕ) (hs : 0 < s) : ProblemParameters where
  n := s
  n_pos := hs
  L := p.L / 2
  L_pos := div_pos p.L_pos (by norm_num)
  gap := p.gap
  gap_pos := p.gap_pos
  epsilon := (3 / 2 : ℝ) * p.epsilon
  epsilon_pos := mul_pos (by norm_num) p.epsilon_pos
  diameter := p.diameter
  diameter_nonneg := p.diameter_nonneg

def sourceIndex (s : ℕ) (hs : 0 < s) {n : ℕ} (i : Fin n) : Fin s :=
  ⟨i.val % s, Nat.mod_lt i.val hs⟩

theorem sourceParameters_A (p : ProblemParameters) (s : ℕ) (hs : 0 < s) :
    dimensionlessA (sourceParameters p s hs) = (2 / 9 : ℝ) * dimensionlessA p := by
  unfold dimensionlessA sourceParameters
  field_simp
  <;> ring

theorem sourceParameters_B (p : ProblemParameters) (s : ℕ) (hs : 0 < s) :
    dimensionlessB (sourceParameters p s hs) = dimensionlessB p / 3 := by
  unfold dimensionlessB sourceParameters
  field_simp
  <;> ring

theorem fin_average_preserved {V : Type*} [AddCommGroup V] [Module ℝ V]
    (n s : ℕ) (hs : 0 < s) (hsn : s ≤ n) (g : Fin s → V) :
    (n : ℝ)⁻¹ • (∑ i : Fin n, weight n s (i.val % s) • g (sourceIndex s hs i)) =
      (s : ℝ)⁻¹ • (∑ j : Fin s, g j) := by
  let G : ℕ → V := fun j ↦ if hj : j < s then g ⟨j, hj⟩ else 0
  have h := finite_average_preserved n s hs hsn G
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at h
  simpa only [one_div, G, Nat.mod_lt _ hs, dite_true, sourceIndex, Fin.isLt] using h

variable {p : ProblemParameters} {s dx dy : ℕ} {hs : 0 < s}
  {K : KnownDualDomain dy p.diameter}

def components (P : Problem (sourceParameters p s hs) dx dy K)
    (i : Fin p.n) (z : JointSpace dx dy) : ℝ :=
  weight p.n s (i.val % s) * P.component (sourceIndex s hs i) z

def gradients (P : Problem (sourceParameters p s hs) dx dy K)
    (i : Fin p.n) (z : JointSpace dx dy) : JointSpace dx dy :=
  weight p.n s (i.val % s) • P.componentGradient (sourceIndex s hs i) z

theorem average_components (P : Problem (sourceParameters p s hs) dx dy K)
    (hsn : s ≤ p.n) (z : JointSpace dx dy) :
    componentAverage (components P) z = componentAverage P.component z := by
  change (p.n : ℝ)⁻¹ • (∑ i : Fin p.n,
      weight p.n s (i.val % s) • P.component (sourceIndex s hs i) z) =
    (s : ℝ)⁻¹ • (∑ j : Fin s, P.component j z)
  exact fin_average_preserved p.n s hs hsn (fun j ↦ P.component j z)

theorem primal_value (P : Problem (sourceParameters p s hs) dx dy K) (hsn : s ≤ p.n) :
    primalObjective K (components P) = primalObjective K P.component := by
  funext x
  simp only [primalObjective, average_components P hsn]

def toProblem (P : Problem (sourceParameters p s hs) dx dy K) (hsn : s ≤ p.n) :
    Problem p dx dy K where
  component := components P
  componentGradient := gradients P
  neighborhood := P.neighborhood
  neighborhood_open := P.neighborhood_open
  domain_subset := P.domain_subset
  gradient_correct := by
    intro i z hz
    rw [hasGradientAt_iff_hasFDerivAt]
    have h := (P.gradient_correct (sourceIndex s hs i) z hz).hasFDerivAt.const_smul
      (weight p.n s (i.val % s))
    convert h using 1
    · rfl
    · simp only [gradients, map_smul]
  average_dual_concave := by
    intro x
    simpa only [average_components P hsn] using P.average_dual_concave x
  initialPoint := P.initialPoint
  value_bddBelow := by rw [primal_value P hsn]; exact P.value_bddBelow
  initial_gap := by rw [primal_value P hsn]; exact P.initial_gap

theorem toProblem_individualSmooth (P : Problem (sourceParameters p s hs) dx dy K)
    (hsn : s ≤ p.n) (hP : P.individualSmooth) : (toProblem P hsn).individualSmooth := by
  intro i z hz w hw
  have hi := Nat.mod_lt i.val hs
  have ha := weight_pos_le_two p.n s (i.val % s) hs hsn hi
  change ‖weight p.n s (i.val % s) • P.componentGradient (sourceIndex s hs i) z -
      weight p.n s (i.val % s) • P.componentGradient (sourceIndex s hs i) w‖ ≤ _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha.1]
  have hb := hP (sourceIndex s hs i) z hz w hw
  change ‖P.componentGradient (sourceIndex s hs i) z -
    P.componentGradient (sourceIndex s hs i) w‖ ≤ (p.L / 2) * ‖z - w‖ at hb
  have hh := mul_le_mul_of_nonneg_left hb ha.1.le
  have hbound := mul_le_mul_of_nonneg_right ha.2
    (mul_nonneg (div_nonneg p.L_pos.le (by norm_num : (0 : ℝ) ≤ 2)) (norm_nonneg (z - w)))
  nlinarith only [hh, hbound]

theorem moreau_target (P : Problem (sourceParameters p s hs) dx dy K) (hsn : s ≤ p.n) :
    problemMoreauEnvelope (toProblem P hsn) =
      moreauEnvelope (primalObjective K P.component) p.L := by
  change moreauEnvelope (primalObjective K (components P)) p.L = _
  rw [primal_value P hsn]

/-- The exact original-model Moreau stationarity transfer, including actual
envelope differentiability at arbitrary, possibly unqueried, output points. -/
theorem stationary_transfer (P : Problem (sourceParameters p s hs) dx dy K)
    (hsn : s ≤ p.n) (hP : P.individualSmooth) (x : PrimalSpace dx)
    (hx : StationaryOutput (toProblem P hsn) x) : StationaryOutput P x := by
  have hAS := P.individual_implies_averaged hP
  apply (P.stationaryOutput_iff hAS x).2
  have ht := ((toProblem P hsn).stationaryOutput_iff
    ((toProblem P hsn).individual_implies_averaged (toProblem_individualSmooth P hsn hP)) x).1 hx
  rw [moreau_target P hsn] at ht
  have hc := moreauEnvelope_parameter_gradient_three_halves p.L_pos
    (P.primal_continuous hAS) P.value_bddBelow (P.primal_weaklyConvex hAS) x
  change ‖gradient (moreauEnvelope (primalObjective K P.component) (p.L / 2)) x‖ ≤
    (3 / 2 : ℝ) * p.epsilon
  exact hc.trans (mul_le_mul_of_nonneg_left ht (by norm_num))

end NCConcave16991.Replication
