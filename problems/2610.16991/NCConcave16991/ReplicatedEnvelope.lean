import NCConcave16991.ReplicationPolicy
import NCConcave16991.EffectiveReplication

/-! # Appendix F.2: deriving the replicated lower envelope

This proves the stated reduction from the high-diameter hard-family theorem
and the smooth baseline, using the actual unrestricted-policy replication
theorem. These two substantive lower-bound hypotheses remain explicit.
-/

noncomputable section

namespace NCConcave16991.Replication

theorem diameter_lower_of_high_and_smooth
    (Ahd Bhd chd Asm csm : ℝ)
    (hAhd : 0 < Ahd) (hBhd : 1 ≤ Bhd) (hchd : 0 < chd)
    (hAsm : 0 < Asm) (hcsm : 0 < csm)
    (hhigh : ∀ q : ProblemParameters, Ahd ≤ dimensionlessA q →
      Bhd * (q.n : ℝ) ^ (1 / 4 : ℝ) ≤ dimensionlessB q →
      LowerBudgetBound q .individual
        (chd * dimensionlessA q * (q.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB q))
    (hsmooth : ∀ q : ProblemParameters, Asm ≤ dimensionlessA q →
      LowerBudgetBound q .individual
        (csm * ((q.n : ℝ) + dimensionlessA q * (q.n : ℝ) ^ (1 / 2 : ℝ)))) :
    ∃ Arep crep : ℝ, 0 < Arep ∧ 0 < crep ∧
      ∀ p : ProblemParameters, Arep ≤ dimensionlessA p →
        LowerBudgetBound p .individual
          (crep * ((p.n : ℝ) + dimensionlessA p * diameterLower (p.n : ℝ) (dimensionlessB p))) := by
  let b : ℝ := 3 * Bhd
  let d : ℝ := chd / (27 * b ^ 3)
  let w : ℝ := min (csm / b ^ 4) d
  have hb : 1 ≤ b := by dsimp [b]; linarith
  have hbpos : 0 < b := by linarith
  have hdpos : 0 < d := div_pos hchd (by positivity)
  have hwpos : 0 < w := lt_min (div_pos hcsm (pow_pos hbpos 4)) hdpos
  have hwb4 : w ≤ csm / b ^ 4 := min_le_left _ _
  have hwd : w ≤ d := min_le_right _ _
  have hb4 : 1 ≤ b ^ 4 := one_le_pow₀ hb
  have hwc : w ≤ csm := hwb4.trans ((div_le_iff₀ (pow_pos hbpos 4)).2 (by nlinarith))
  refine ⟨max ((9 / 2 : ℝ) * Ahd) Asm, w / 2, ?_, by positivity, ?_⟩
  · exact lt_of_lt_of_le hAsm (le_max_right _ _)
  intro p hA T hT
  have hAsm' := (le_max_right ((9 / 2 : ℝ) * Ahd) Asm).trans hA
  have hAhd' := (le_max_left ((9 / 2 : ℝ) * Ahd) Asm).trans hA
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  have hAnn := (dimensionlessA_pos p).le
  have hBnn := dimensionlessB_nonneg p
  have hFnn : 0 ≤ diameterLower (p.n : ℝ) (dimensionlessB p) :=
    le_min (pow_nonneg hBnn _) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hBnn)
  have hsm := hsmooth p hAsm' T hT
  have hsqrt : 0 ≤ (p.n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hB : b ≤ dimensionlessB p
  · let s := effectiveCount p.n (dimensionlessB p) b
    have hsb := effectiveCount_bounds p.n_pos hbpos hB
    have hs : 0 < s := hsb.1
    have hsn : s ≤ p.n := hsb.2.1
    have hqA : Ahd ≤ dimensionlessA (sourceParameters p s hs) := by
      rw [sourceParameters_A]
      linarith only [hAhd']
    have hquarter := effectiveCount_quarter_bound p.n_pos hbpos hB
    have hBhdpos : 0 < Bhd := by linarith
    have hqid : Bhd * (dimensionlessB p / b) = dimensionlessB p / 3 := by
      dsimp [b]
      field_simp
      <;> ring
    have hqB : Bhd * ((sourceParameters p s hs).n : ℝ) ^ (1 / 4 : ℝ) ≤
        dimensionlessB (sourceParameters p s hs) := by
      rw [sourceParameters_B]
      change Bhd * (s : ℝ) ^ (1 / 4 : ℝ) ≤ dimensionlessB p / 3
      rw [← hqid]
      exact mul_le_mul_of_nonneg_left hquarter hBhdpos.le
    have hhd := lowerBudget_transfer p s hs hsn
      (hhigh (sourceParameters p s hs) hqA hqB) T hT
    rw [sourceParameters_A, sourceParameters_B] at hhd
    have hdiam := diameterLower_le_effectiveCount p.n_pos hb hB
    have hscale := mul_le_mul_of_nonneg_left hdiam (mul_nonneg hdpos.le hAnn)
    have hid : d * dimensionlessA p *
        (2 * b ^ 3 * dimensionlessB p * (s : ℝ) ^ (3 / 4 : ℝ)) =
        chd * ((2 / 9 : ℝ) * dimensionlessA p) *
          (s : ℝ) ^ (3 / 4 : ℝ) * (dimensionlessB p / 3) := by
      dsimp [d]
      field_simp
      <;> ring
    rw [hid] at hscale
    have hnonlinear : d * dimensionlessA p * diameterLower (p.n : ℝ) (dimensionlessB p) ≤ T :=
      hscale.trans hhd
    have hwlinear := mul_le_mul_of_nonneg_right hwc (Nat.cast_nonneg p.n)
    have hwnonlinear := mul_le_mul_of_nonneg_right hwd (mul_nonneg hAnn hFnn)
    have hsmlinear : csm * (p.n : ℝ) ≤ T := by
      nlinarith only [hsm, mul_nonneg hcsm.le (mul_nonneg hAnn hsqrt)]
    nlinarith only [hwlinear, hwnonlinear, hnonlinear, hsmlinear]
  · have hB' : dimensionlessB p ≤ b := le_of_not_ge hB
    have hpower : dimensionlessB p ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ hBnn hB' _
    have hsqrt1 : 1 ≤ (p.n : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hn (by norm_num)
    have hF : diameterLower (p.n : ℝ) (dimensionlessB p) ≤
        b ^ 4 * (p.n : ℝ) ^ (1 / 2 : ℝ) := by
      exact (min_le_left _ _).trans (hpower.trans (le_mul_of_one_le_right (by positivity) hsqrt1))
    have hwhole : (p.n : ℝ) + dimensionlessA p * diameterLower (p.n : ℝ) (dimensionlessB p) ≤
        b ^ 4 * ((p.n : ℝ) + dimensionlessA p * (p.n : ℝ) ^ (1 / 2 : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hF hAnn
      have h2 := mul_le_mul_of_nonneg_right hb4 (Nat.cast_nonneg p.n)
      nlinarith only [h1, h2]
    have hcoef : w / 2 ≤ csm / b ^ 4 := (show w / 2 ≤ w by linarith).trans hwb4
    have hwhole0 : 0 ≤ (p.n : ℝ) + dimensionlessA p * diameterLower (p.n : ℝ) (dimensionlessB p) :=
      add_nonneg (Nat.cast_nonneg _) (mul_nonneg hAnn hFnn)
    have hc1 := mul_le_mul_of_nonneg_right hcoef hwhole0
    have hc2 := mul_le_mul_of_nonneg_left hwhole (div_nonneg hcsm.le (pow_nonneg hbpos.le 4))
    have hid : csm / b ^ 4 *
        (b ^ 4 * ((p.n : ℝ) + dimensionlessA p * (p.n : ℝ) ^ (1 / 2 : ℝ))) =
        csm * ((p.n : ℝ) + dimensionlessA p * (p.n : ℝ) ^ (1 / 2 : ℝ)) := by
      field_simp
    rw [hid] at hc2
    exact hc1.trans (hc2.trans hsm)

end NCConcave16991.Replication
