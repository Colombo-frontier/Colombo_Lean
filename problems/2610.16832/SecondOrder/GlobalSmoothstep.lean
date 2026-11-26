import SecondOrder.Smoothstep
import SecondOrder.ClippedCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace SecondOrder
noncomputable section

def gateFirst : ℝ → ℝ := unitClipped gateD1
def gateSecond : ℝ → ℝ := unitClipped gateD2
def gateThird : ℝ → ℝ := unitClipped gateD3

theorem gate_eq_unitClipped : gate = unitClipped gatePoly := by
  funext x
  by_cases h0 : x ≤ 0
  · simp [gate, unitClipped, joinAt, h0, gatePoly]
  · by_cases h1 : x < 1
    · simp [gate, unitClipped, joinAt, h0, h1.le, not_le.mpr h1]
    · have h1' : 1 ≤ x := le_of_not_gt h1
      by_cases he : x = 1
      · subst x; norm_num [gate, unitClipped, joinAt, gatePoly]
      · norm_num [gate, unitClipped, joinAt, h0, h1', not_le.mpr (lt_of_le_of_ne h1' (Ne.symm he)), gatePoly]

theorem gate_hasDerivAt (x : ℝ) : HasDerivAt gate (gateFirst x) x := by
  rw [gate_eq_unitClipped]
  exact unitClipped_hasDerivAt gatePoly gateD1 gatePoly_hasDerivAt
    (by norm_num [gateD1]) (by norm_num [gateD1]) x

theorem gateFirst_hasDerivAt (x : ℝ) : HasDerivAt gateFirst (gateSecond x) x :=
  unitClipped_hasDerivAt gateD1 gateD2 gateD1_hasDerivAt
    (by norm_num [gateD2]) (by norm_num [gateD2]) x

theorem gateSecond_hasDerivAt (x : ℝ) : HasDerivAt gateSecond (gateThird x) x :=
  unitClipped_hasDerivAt gateD2 gateD3 gateD2_hasDerivAt
    (by norm_num [gateD3]) (by norm_num [gateD3]) x

theorem deriv_gate : deriv gate = gateFirst := funext (fun x => (gate_hasDerivAt x).deriv)
theorem deriv_gateFirst : deriv gateFirst = gateSecond := funext (fun x => (gateFirst_hasDerivAt x).deriv)
theorem deriv_gateSecond : deriv gateSecond = gateThird := funext (fun x => (gateSecond_hasDerivAt x).deriv)

theorem gateThird_continuous : Continuous gateThird := by
  apply unitClipped_continuous
  unfold gateD3
  fun_prop

theorem gateSecond_contDiff_one : ContDiff ℝ 1 gateSecond := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (gateSecond_hasDerivAt x).differentiableAt, ?_⟩
  rw [deriv_gateSecond]
  exact gateThird_continuous

theorem gateFirst_contDiff_two : ContDiff ℝ 2 gateFirst := by
  rw [show (2:WithTop ℕ∞) = 1+1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (gateFirst_hasDerivAt x).differentiableAt, by simp, ?_⟩
  rw [deriv_gateFirst]
  exact gateSecond_contDiff_one

/-- The actual piecewise gate is C³ on all of ℝ, including both junctions. -/
theorem gate_contDiff_three : ContDiff ℝ 3 gate := by
  rw [show (3:WithTop ℕ∞) = 2+1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (gate_hasDerivAt x).differentiableAt, by simp, ?_⟩
  rw [deriv_gate]
  exact gateFirst_contDiff_two

def gateD4 (t : ℝ) : ℝ := 840-10080*t+25200*t^2-16800*t^3

theorem gateD3_hasDerivAt (t : ℝ) : HasDerivAt gateD3 (gateD4 t) t := by
  convert (((hasDerivAt_id t).const_mul 840).sub
    (((hasDerivAt_id t).pow 2).const_mul 5040) |>.add
    (((hasDerivAt_id t).pow 3).const_mul 8400) |>.sub
    (((hasDerivAt_id t).pow 4).const_mul 4200)) using 1
  · funext z; dsimp [gateD3]; ring
  · dsimp [gateD4]; ring

theorem gateD4_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖gateD4 t‖ ≤ 52920 := by
  have ha : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have h2 : |t^2| ≤ 1 := by simpa only [abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg t) ha 2
  have h3 : |t^3| ≤ 1 := by simpa only [abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg t) ha 3
  calc
    ‖gateD4 t‖ ≤ |840|+|10080*t|+|25200*t^2|+|16800*t^3| := by
      simpa only [gateD4, Real.norm_eq_abs] using
        (abs_sub (840-10080*t+25200*t^2) (16800*t^3)).trans
          (add_le_add_right ((abs_add (840-10080*t) (25200*t^2)).trans
            (add_le_add_right (abs_sub (840:ℝ) (10080*t)) _)) _)
    _ ≤ 52920 := by
      simp only [abs_mul]
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 840),
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 10080),
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 25200),
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 16800)]
      linarith

theorem gateThird_lipschitz_bound (x y : ℝ) :
    ‖gateThird y-gateThird x‖ ≤ 52920*‖y-x‖ :=
  unitClipped_lipschitz_bound gateD3 gateD4 gateD3_hasDerivAt (by norm_num)
    (fun _ ht => gateD4_bound ht) x y

theorem gateThird_lipschitz : LipschitzWith 52920 gateThird := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using gateThird_lipschitz_bound y x

/-- C^{3,1}: C³ together with a globally Lipschitz actual third scalar derivative. -/
theorem gate_C31 : ContDiff ℝ 3 gate ∧ LipschitzWith 52920 (deriv (deriv (deriv gate))) := by
  rw [deriv_gate, deriv_gateFirst, deriv_gateSecond]
  exact ⟨gate_contDiff_three, gateThird_lipschitz⟩

end
end SecondOrder
