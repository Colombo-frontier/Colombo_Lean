import ExactValue.SCModel

open scoped InnerProductSpace ENNReal
set_option autoImplicit false
namespace ExactValue
noncomputable section

def shiftedQuadratic {d : ℕ} (lam : ℝ) (z x : Euclid d) : ℝ := lam / 2 * ‖x - z‖ ^ 2

theorem shiftedQuadratic_derivative {d : ℕ} (lam : ℝ) (z x : Euclid d) :
    HasFDerivAt (shiftedQuadratic lam z) (innerSL ℝ (lam • (x - z))) x := by
  have hn := (hasStrictFDerivAt_norm_sq (x - z)).hasFDerivAt
  convert (hn.comp x ((hasFDerivAt_id x).sub_const z)).const_mul (lam / 2) using 1
  ext w
  simp [innerSL_apply, real_inner_smul_left]
  ring

theorem shiftedQuadratic_remainder {d : ℕ} (lam : ℝ) (z x y : Euclid d) :
    shiftedQuadratic lam z y + ⟪lam • (y - z), x - y⟫_ℝ + lam / 2 * ‖x - y‖ ^ 2 =
      shiftedQuadratic lam z x := by
  unfold shiftedQuadratic
  simp only [norm_sub_sq_real, real_inner_smul_left, inner_sub_left, inner_sub_right]
  rw [real_inner_comm z x, real_inner_comm z y, real_inner_comm y x,
    real_inner_self_eq_norm_sq]
  ring

theorem shiftedQuadratic_strong {d : ℕ} (lam : ℝ) (z : Euclid d) :
    StrongConvexOn Set.univ lam (shiftedQuadratic lam z) := by
  apply (strong_iff_supporting (shiftedQuadratic_derivative lam z)).mpr
  exact fun x y => (shiftedQuadratic_remainder lam z x y).le

theorem shiftedQuadratic_admissible {d : ℕ} {μ lam β R : ℝ} (hlam : 0 < lam)
    (hμlam : μ ≤ lam) (hlamβ : lam ≤ β) (z : Euclid d) (hz : ‖z‖ ≤ R / 2) :
    SCObjective d μ β R (shiftedQuadratic lam z) := by
  have hs := shiftedQuadratic_strong lam z
  refine ⟨⟨hs.strictConvexOn hlam |>.convexOn, ?_, ?_, ?_⟩, hs.mono hμlam⟩
  · exact (contDiff_const (c := lam / 2)).mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  · refine ⟨fun x => lam • (x - z), shiftedQuadratic_derivative lam z, ?_⟩
    intro x y
    rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
    exact mul_le_mul_of_nonneg_right hlamβ (norm_nonneg _)
  · have hmin : ∀ y, shiftedQuadratic lam z z ≤ shiftedQuadratic lam z y := by
      intro y
      simp only [shiftedQuadratic, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero]
      positivity
    refine ⟨z, hz, hmin, ?_⟩
    intro w hw
    have h := hw z
    have hz0 : shiftedQuadratic lam z z = 0 := by simp [shiftedQuadratic]
    rw [hz0] at h
    have hn : ‖w - z‖ = 0 := by
      dsimp [shiftedQuadratic] at h
      by_contra hn
      have hp : 0 < ‖w - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
      exact (not_lt_of_ge h) (mul_pos (by positivity) (sq_pos_of_pos hp))
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem shiftedQuadratic_orthogonal {d : ℕ} (lam r : ℝ) {v x : Euclid d}
    (hv : ‖v‖ = 1) (hx : ⟪x, v⟫_ℝ = 0) :
    shiftedQuadratic lam (r • v) x = lam / 2 * (‖x‖ ^ 2 + r ^ 2) := by
  simp [shiftedQuadratic, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hv,
    inner_smul_right, hx, sq_abs]

/-- A replay lemma for two fixed objectives that coincide along one actual history. -/
theorem policyHistory_eq_of_values {d T : ℕ} {R : ℝ} (A : ValueAlgorithm d R T)
    (f g : Euclid d → ℝ) (N : ℕ)
    (h : ∀ n < N, f (A.query n (policyHistory A.query f n)) =
      g (A.query n (policyHistory A.query f n))) :
    policyHistory A.query f N = policyHistory A.query g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hp := ih (fun n hn => h n (by omega))
    simp only [policyHistory]
    rw [← hp, ← h N (by omega)]

/-- A hidden shift survives T scalar queries and an unqueried terminal output. -/
theorem hidden_shift_lower {d T : ℕ} (hTd : T + 1 < d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε)
    (hεmax : ε ≤ β * R ^ 2 / 64) (A : ValueAlgorithm d R T) :
    ∃ f : Euclid d → ℝ, SCObjective d μ β R f ∧
      ∃ xstar : Euclid d, (∀ y, f xstar ≤ f y) ∧ 2 * ε ≤ f (A.result f) - f xstar := by
  let lam := max μ (64 * ε / R ^ 2)
  let r := R / 4
  let fake : Euclid d → ℝ := fun x => lam / 2 * (‖x‖ ^ 2 + r ^ 2)
  let pts : Fin (T + 1) → Euclid d := Fin.snoc
    (fun n : Fin T => (A.query n.val (policyHistory A.query fake n.val) : Euclid d)) (A.result fake)
  obtain ⟨v, hv, hk⟩ := exists_unit_frame_kernel hTd pts
  have horth (i : Fin (T + 1)) : ⟪pts i, v⟫_ℝ = 0 := by
    have h := congrArg (fun w : Euclid (T + 1) => w i) hk
    simpa only [frameRead_apply, PiLp.zero_apply] using h
  have hlam : 0 < lam := hμ.trans_le (le_max_left _ _)
  have hlamβ : lam ≤ β := by
    apply max_le hμβ
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    linarith
  let f := shiftedQuadratic lam (r • v)
  have hf : SCObjective d μ β R f := shiftedQuadratic_admissible hlam (le_max_left _ _) hlamβ _ (by
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one, abs_of_pos (show 0 < r by dsimp [r]; positivity)]
    dsimp [r]
    linarith)
  have hqueries (n : ℕ) (hn : n < T) :
      fake (A.query n (policyHistory A.query fake n)) = f (A.query n (policyHistory A.query fake n)) := by
    have ho := horth (Fin.castSucc ⟨n, hn⟩)
    simp only [pts, Fin.snoc_castSucc] at ho
    exact (shiftedQuadratic_orthogonal lam r hv ho).symm
  have hhist := policyHistory_eq_of_values A fake f T hqueries
  have hout : A.result fake = A.result f := congrArg (fun h => (A.output h : Euclid d)) hhist
  have ho := horth (Fin.last T)
  simp only [pts, Fin.snoc_last] at ho
  have hvalue := shiftedQuadratic_orthogonal lam r hv ho
  rw [hout] at hvalue
  have hmin : ∀ y, f (r • v) ≤ f y := by
    intro y
    change shiftedQuadratic lam (r • v) (r • v) ≤ shiftedQuadratic lam (r • v) y
    simp only [shiftedQuadratic, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero]
    positivity
  refine ⟨f, hf, r • v, hmin, ?_⟩
  have hlame : 64 * ε / R ^ 2 ≤ lam := le_max_right _ _
  have hlame' := (div_le_iff₀ (sq_pos_of_pos hR)).mp hlame
  change 2 * ε ≤ shiftedQuadratic lam (r • v) (A.result f) - shiftedQuadratic lam (r • v) (r • v)
  rw [hvalue]
  simp only [shiftedQuadratic, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, sub_zero]
  dsimp [r]
  nlinarith [mul_nonneg hlam.le (sq_nonneg ‖A.result f‖)]

theorem sc_quadratic_lower {d : ℕ} (hd : 2 ≤ d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε)
    (hεmax : ε ≤ β * R ^ 2 / 64) :
    ENNReal.ofReal ((d : ℝ) - 1) ≤ scValueComplexity d R μ β ε := by
  apply sc_lower_of_failure
  intro T hT A hA
  have hTd : T + 1 < d := by
    have : (T + 1 : ℝ) < d := by linarith
    exact_mod_cast this
  obtain ⟨f, hf, x, hx, hbad⟩ := hidden_shift_lower hTd hμ hμβ hR hε hεmax A
  obtain ⟨z, hz, hgood⟩ := hA f hf
  have := hx z
  have := hz x
  linarith

end
end ExactValue
