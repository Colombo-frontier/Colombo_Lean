import GradientHessian.LatchChain

/-! Global value estimates for the literal scaled latch potential. -/

noncomputable section
namespace GradientHessian.LatchChain

open EuclideanRegisters Profiles IntegralProfiles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def publicQuadratic (n : ℕ) (r : Fin (n + 1) → ℝ) (U : Registers E (n + 1)) : ℝ :=
  ∑ i, (4 / r i) * ‖U i‖ ^ 2

def residual (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ)
    (U : Registers E (n + 1)) : ℝ := self n v r 0 U - publicQuadratic n r U

theorem publicQuadratic_succ (n : ℕ) (r : Fin (n + 2) → ℝ) (U : Registers E (n + 2)) :
    publicQuadratic (n + 1) r U = (4 / r 0) * ‖U 0‖ ^ 2 +
      publicQuadratic n (fun i => r i.succ) (tail E (n + 1) U) := by
  rw [publicQuadratic, Fin.sum_univ_succ]
  rfl

theorem incoming_bounds {r : ℝ} (hr : 0 ≤ r) (v x : E) :
    0 ≤ incoming r v x ∧ incoming r v x ≤ 56 * r := by
  refine ⟨incoming_nonneg hr v x, ?_⟩
  have hc := chi_bounds (u r v x)
  have he := ell₀_bounds (u r v x)
  have hm : (1 - chi (u r v x)) * ell₀ (u r v x) ≤ 7 := by
    nlinarith only [hc.1, hc.2, he.1, he.2,
      mul_nonneg hc.1 (show 0 ≤ ell₀ (u r v x) by linarith only [he.1])]
  have hh := mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hr)
  unfold incoming
  nlinarith only [hh]

theorem atom_residual_eq {r : ℝ} (hr : r ≠ 0) (a : ℝ) (v x : E) :
    atom a r v x - (4 / r) * ‖x‖ ^ 2 =
      -8 * r * (chi (u r v x) + (1 - chi (u r v x)) * a) * ell₀ (u r v x) := by
  simp only [atom, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

theorem atom_residual_bounds {a r : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 < r)
    (v x : E) :
    -56 * r ≤ atom a r v x - (4 / r) * ‖x‖ ^ 2 ∧
      atom a r v x - (4 / r) * ‖x‖ ^ 2 ≤ 0 := by
  rw [atom_residual_eq hr.ne']
  let c := chi (u r v x) + (1 - chi (u r v x)) * a
  have hc := chi_bounds (u r v x)
  have he := ell₀_bounds (u r v x)
  have hc0 : 0 ≤ c := add_nonneg hc.1 (mul_nonneg (by linarith only [hc.2]) ha0)
  have hc1 : c ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left ha1 (show 0 ≤ 1 - chi (u r v x) by linarith only [hc.2])
    dsimp [c]
    linarith only [h]
  have he0 : 0 ≤ ell₀ (u r v x) := by linarith only [he.1]
  have hm0 := mul_nonneg hc0 he0
  have hm1 : c * ell₀ (u r v x) ≤ 7 := by
    have h := mul_le_mul_of_nonneg_right hc1 he0
    linarith only [h, he.2]
  have h0 := mul_nonneg hr.le hm0
  have h1 := mul_le_mul_of_nonneg_left hm1 hr.le
  change -56 * r ≤ -8 * r * c * ell₀ (u r v x) ∧ -8 * r * c * ell₀ (u r v x) ≤ 0
  constructor <;> nlinarith only [h0, h1]

theorem self_residual_bounds (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ)
    (hr : ∀ i, 0 < r i) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (U : Registers E (n + 1)) :
    -56 * (∑ i, r i) ≤ self n v r a U - publicQuadratic n r U ∧
      self n v r a U - publicQuadratic n r U ≤ 0 := by
  induction n generalizing a with
  | zero =>
    simpa [self, publicQuadratic] using atom_residual_bounds ha0 ha1 (hr 0) (v 0) (U 0)
  | succ n ih =>
    have hhead := atom_residual_bounds ha0 ha1 (hr 0) (v 0) (U 0)
    have ht := ih (fun i => v i.succ) (fun i => r i.succ) (fun i => hr i.succ)
      (chi_bounds (u (r 0) (v 0) (U 0))).1 (chi_bounds (u (r 0) (v 0) (U 0))).2
      (tail E (n + 1) U)
    rw [self, publicQuadratic_succ, Fin.sum_univ_succ]
    constructor <;> linarith only [hhead.1, hhead.2, ht.1, ht.2]

theorem sourceScale_sum (n : ℕ) (s : ℝ) :
    (∑ i : Fin (n + 1), sourceScale s i) = s * ((2 : ℝ) ^ (n + 1) - 1) := by
  induction n generalizing s with
  | zero => norm_num [sourceScale]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have he : (∑ i : Fin (n + 1), sourceScale s i.succ) =
        ∑ i : Fin (n + 1), sourceScale (2 * s) i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [sourceScale, Fin.val_succ, pow_succ]
      ring
    rw [he, ih]
    simp only [sourceScale, Fin.val_zero, pow_zero, mul_one, pow_succ]
    ring

theorem sourceScale_sum_le (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (∑ i : Fin (n + 1), sourceScale s i) ≤ 2 * sourceScale s (Fin.last n) := by
  rw [sourceScale_sum]
  simp only [sourceScale, Fin.val_last, pow_succ]
  nlinarith only [hs]

/-- Both value inequalities in the manuscript's latch lemma, on its exact
geometric scales and public quadratic. No dimension enters either bound. -/
theorem source_value_bounds (n : ℕ) (v : Fin (n + 2) → E) {s : ℝ} (hs : 1 ≤ s)
    (U : Registers E (n + 2)) :
    (0 ≤ incoming s (v 0) (U 0) ∧ incoming s (v 0) (U 0) ≤ 56 * s) ∧
      (-112 * sourceScale s (Fin.last (n + 1)) ≤ residual (n + 1) v (sourceScale s) U ∧
        residual (n + 1) v (sourceScale s) U ≤ 0) := by
  refine ⟨incoming_bounds (by linarith) _ _, ?_⟩
  have hb := self_residual_bounds (n + 1) v (sourceScale s)
    (sourceScale_pos (by linarith)) (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) U
  have hsumm := sourceScale_sum_le (n + 1) (by linarith : 0 ≤ s)
  change -112 * sourceScale s (Fin.last (n + 1)) ≤
      self (n + 1) v (sourceScale s) 0 U - publicQuadratic (n + 1) (sourceScale s) U ∧ _
  exact ⟨by linarith only [hb.1, hsumm], hb.2⟩

end GradientHessian.LatchChain
