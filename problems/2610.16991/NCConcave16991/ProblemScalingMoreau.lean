import NCConcave16991.ProblemScaling

/-! # Actual proximal and Moreau-gradient scaling -/

noncomputable section

open Set
open scoped InnerProductSpace

namespace NCConcave16991.ProblemScaling

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  {a b : ℝ}

theorem proxObjective_scale (P : Problem p dx dy K) (ha : 0 < a) (hb : 0 < b)
    (c x : PrimalSpace dx) :
    proxObjective (primalObjective (dualDomain K b hb) (components P a b))
      (a * b ^ 2 * p.L) c x =
      a * proxObjective (primalObjective K P.component) p.L (b • c) (b • x) := by
  rw [proxObjective, proxObjective, primal_value P ha hb, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos hb, mul_pow]
  ring

def scaledProx (P : Problem p dx dy K) (hP : P.individualSmooth) (b : ℝ)
    (c : PrimalSpace dx) : PrimalSpace dx :=
  b⁻¹ • proximalMap p.L_pos (P.primal_continuous (P.individual_implies_averaged hP))
    P.value_bddBelow (b • c)

theorem scaledProx_spec (P : Problem p dx dy K) (hP : P.individualSmooth)
    (ha : 0 < a) (hb : 0 < b) (c : PrimalSpace dx) :
    IsProxPoint (primalObjective (dualDomain K b hb) (components P a b))
      (a * b ^ 2 * p.L) c (scaledProx P hP b c) := by
  intro x
  rw [proxObjective_scale P ha hb, proxObjective_scale P ha hb]
  have hs : b • scaledProx P hP b c =
      proximalMap p.L_pos (P.primal_continuous (P.individual_implies_averaged hP))
        P.value_bddBelow (b • c) := by
    simp only [scaledProx, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  rw [hs]
  exact mul_le_mul_of_nonneg_left
    (proximalMap_spec p.L_pos (P.primal_continuous (P.individual_implies_averaged hP))
      P.value_bddBelow (b • c) (b • x)) ha.le

theorem scaled_residual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L a b : ℝ) (hb : b ≠ 0) (c u : E) :
    (2 * (a * b ^ 2 * L)) • (c - b⁻¹ • u) =
      (a * b) • ((2 * L) • (b • c - u)) := by
  simp only [smul_sub, smul_smul]
  congr 1
  · congr 1
    ring
  · congr 1
    field_simp
    <;> ring

theorem moreau_scaled_hasGradientAt (P : Problem p dx dy K) (hP : P.individualSmooth)
    (ha : 0 < a) (hb : 0 < b) (c : PrimalSpace dx) :
    HasGradientAt (problemMoreauEnvelope (toProblem P ha hb))
      ((a * b) • gradient (problemMoreauEnvelope P) (b • c)) c := by
  have hAS := P.individual_implies_averaged hP
  have hSAS := (toProblem P ha hb).individual_implies_averaged (toProblem_individualSmooth P ha hb hP)
  have hh := moreauEnvelope_hasGradientAt (parameters p a b ha hb).L_pos
    ((toProblem P ha hb).primal_weaklyConvex hSAS) (scaledProx_spec P hP ha hb) c
  change HasGradientAt (problemMoreauEnvelope (toProblem P ha hb))
    ((2 * (a * b ^ 2 * p.L)) • (c - scaledProx P hP b c)) c at hh
  rw [scaledProx, scaled_residual p.L a b hb.ne', ← (P.moreau_hasGradientAt hAS (b • c)).gradient] at hh
  exact hh

/-- The exact public-accuracy scaling applies to every arbitrary output point. -/
theorem stationary_transfer (P : Problem p dx dy K) (hP : P.individualSmooth)
    (ha : 0 < a) (hb : 0 < b) (c : PrimalSpace dx)
    (hc : StationaryOutput (toProblem P ha hb) c) : StationaryOutput P (b • c) := by
  obtain ⟨g, hg, hn⟩ := hc
  have hnew := moreau_scaled_hasGradientAt P hP ha hb c
  have hEq : g = (a * b) • gradient (problemMoreauEnvelope P) (b • c) := hg.unique hnew
  rw [hEq, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos ha hb)] at hn
  apply (P.stationaryOutput_iff (P.individual_implies_averaged hP) (b • c)).2
  change a * b * ‖gradient (problemMoreauEnvelope P) (b • c)‖ ≤ a * b * p.epsilon at hn
  exact (mul_le_mul_iff_right₀ (mul_pos ha hb)).1 hn

end NCConcave16991.ProblemScaling
