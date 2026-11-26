import MinimaxAudit.IdealGap
import MinimaxAudit.CriterionFull
import MinimaxAudit.Geometry
import MinimaxAudit.StrongSaddle

open scoped ContDiff

/-! The ideal gap witness on actual Euclidean primal/dual frames. -/
open scoped RealInnerProductSpace
namespace MinimaxAudit

noncomputable def weightWitness {n d : ℕ} {U : Fin (n+1) → Primal d}
    (hU : Orthonormal ℝ U) (q s : ℝ) : Primal d :=
  (s / Real.sqrt 2) • frameSynthesis hU (WithLp.toLp 2 (sourceWeight q n))

theorem weightWitness_inner {n d : ℕ} {U : Fin (n+1) → Primal d}
    (hU : Orthonormal ℝ U) (q s : ℝ) (i : Fin (n+1)) :
    inner ℝ (U i) (weightWitness hU q s) = s / Real.sqrt 2 * sourceWeight q n i := by
  unfold weightWitness
  rw [inner_smul_right]
  change _ * inner ℝ (U i) (∑ j, sourceWeight q n j • U j) = _
  rw [hU.inner_right_fintype]

theorem weightWitness_norm_sq {n d : ℕ} {U : Fin (n+1) → Primal d}
    (hU : Orthonormal ℝ U) (q s : ℝ) :
    ‖weightWitness hU q s‖ ^ 2 = s ^ 2 / 2 * ∑ i : Fin (n+1), (sourceWeight q n i) ^ 2 := by
  unfold weightWitness
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, (frameSynthesis hU).norm_map,
    EuclideanSpace.real_norm_sq_eq]
  simp [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem weightWitness_inner_left {n d : ℕ} {U : Fin (n+1) → Primal d}
    (hU : Orthonormal ℝ U) (q s : ℝ) (x : Primal d) :
    inner ℝ x (weightWitness hU q s) =
      s / Real.sqrt 2 * ∑ i : Fin (n+1), sourceWeight q n i * inner ℝ (U i) x := by
  simp [weightWitness, frameSynthesis, frameSynthesisLinear, inner_smul_right,
    inner_sum, real_inner_comm, Finset.mul_sum]

section Witness
variable {n dx dy : ℕ} {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
variable (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)

theorem pairedA_join (i : Fin (n+1)) (x : Primal dx) (y : Dual dy) :
    pairedA U V i (joinBlocks x y) =
      (inner ℝ (U i) x + inner ℝ (V i) y) / Real.sqrt 2 := by
  exact paired_plus_coordinate U V i x y

theorem pairedB_join (i : Fin (n+1)) (x : Primal dx) (y : Dual dy) :
    pairedB U V i (joinBlocks x y) =
      (inner ℝ (U i) x - inner ℝ (V i) y) / Real.sqrt 2 := by
  exact paired_minus_coordinate U V i x y

theorem pairedA_primal_witness (q s : ℝ) (i : Fin (n+1)) (x : Primal dx) (y : Dual dy) :
    pairedA U V i (joinBlocks (x + weightWitness hU q s) y) =
      pairedA U V i (joinBlocks x y) + s * sourceWeight q n i / 2 := by
  rw [pairedA_join, pairedA_join, inner_add_right, weightWitness_inner hU]
  simp only [div_eq_mul_inv]
  ring_nf
  rw [sqrt_two_inv_sq]
  ring

theorem pairedA_dual_witness (q s : ℝ) (i : Fin (n+1)) (x : Primal dx) (y : Dual dy) :
    pairedA U V i (joinBlocks x (y + weightWitness hV q s)) =
      pairedA U V i (joinBlocks x y) + s * sourceWeight q n i / 2 := by
  rw [pairedA_join, pairedA_join, inner_add_right, weightWitness_inner hV]
  simp only [div_eq_mul_inv]
  ring_nf
  rw [sqrt_two_inv_sq]
  ring

theorem pairedB_primal_witness (q s : ℝ) (i : Fin (n+1)) (x : Primal dx) (y : Dual dy) :
    pairedB U V i (joinBlocks (x + weightWitness hU q s) y) =
      pairedB U V i (joinBlocks x y) + s * sourceWeight q n i / 2 := by
  rw [pairedB_join, pairedB_join, inner_add_right, weightWitness_inner hU]
  simp only [div_eq_mul_inv]
  ring_nf
  rw [sqrt_two_inv_sq]
  ring

theorem pairedB_dual_witness (q s : ℝ) (i : Fin (n+1)) (x : Primal dx) (y : Dual dy) :
    pairedB U V i (joinBlocks x (y + weightWitness hV q s)) =
      pairedB U V i (joinBlocks x y) - s * sourceWeight q n i / 2 := by
  rw [pairedB_join, pairedB_join, inner_add_right, weightWitness_inner hV]
  simp only [div_eq_mul_inv]
  ring_nf
  rw [sqrt_two_inv_sq]
  ring

noncomputable def witnessBase (x : Primal dx) (y : Dual dy) : ℝ := ‖x‖ ^ 2 / 2 - ‖y‖ ^ 2 / 2

theorem witness_base_difference (q s : ℝ) (x : Primal dx) (y : Dual dy) :
    witnessBase x (y + weightWitness hV q s) -
      witnessBase (x + weightWitness hU q s) y =
      -s * (∑ i : Fin (n+1), sourceWeight q n i * pairedA U V i (joinBlocks x y)) -
      s ^ 2 / 2 * (∑ i : Fin (n+1), (sourceWeight q n i) ^ 2) := by
  have hx := norm_add_sq_real x (weightWitness hU q s)
  have hy := norm_add_sq_real y (weightWitness hV q s)
  have hnx := weightWitness_norm_sq hU q s
  have hny := weightWitness_norm_sq hV q s
  have hA : (∑ i : Fin (n+1), sourceWeight q n i * pairedA U V i (joinBlocks x y)) =
      ((∑ i : Fin (n+1), sourceWeight q n i * inner ℝ (U i) x) +
       (∑ i : Fin (n+1), sourceWeight q n i * inner ℝ (V i) y)) / Real.sqrt 2 := by
    calc
      _ = ∑ i : Fin (n+1),
          (sourceWeight q n i * inner ℝ (U i) x + sourceWeight q n i * inner ℝ (V i) y) /
            Real.sqrt 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [pairedA_join]
        ring
      _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hinner : inner ℝ x (weightWitness hU q s) + inner ℝ y (weightWitness hV q s) =
      s * (∑ i : Fin (n+1), sourceWeight q n i * pairedA U V i (joinBlocks x y)) := by
    rw [weightWitness_inner_left hU, weightWitness_inner_left hV, hA]
    ring
  unfold witnessBase
  linear_combination -(1 / 2 : ℝ) * hx - (1 / 2 : ℝ) * hy - hinner -
    (1 / 2 : ℝ) * hnx - (1 / 2 : ℝ) * hny

end Witness

noncomputable def idealHardPotential {n dx dy : ℕ} (lam q c : ℝ)
    (U : Fin (n+1) → Primal dx) (V : Fin (n+1) → Dual dy)
    (z : SaddleSpace dx dy) : ℝ :=
  lam * idealScalarValue q c (witnessBase (primalBlock z) (dualBlock z))
    (fun i => pairedA U V i z) (fun i => pairedB U V i z)

theorem idealHardPotential_witness_exact {n dx dy : ℕ} (lam q c s : ℝ)
    {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (x : Primal dx) (y : Dual dy)
    (hs : s = q ^ n * c - pairedA U V (Fin.last n) (joinBlocks x y)) :
    idealHardPotential lam q c U V (joinBlocks x (y + weightWitness hV q s)) -
      idealHardPotential lam q c U V (joinBlocks (x + weightWitness hU q s) y) =
      lam / 2 * s ^ 2 := by
  unfold idealHardPotential
  rw [← mul_sub]
  simp only [primal_join, dual_join]
  simp_rw [pairedA_primal_witness hU, pairedA_dual_witness hV,
    pairedB_primal_witness hU, pairedB_dual_witness hV]
  rw [idealScalarValue_witness_difference q c s _ _ n _ _ (witness_base_difference hU hV q s x y)]
  rw [← hs]
  ring

theorem idealHardPotential_continuous {n dx dy : ℕ} (lam q c : ℝ)
    (U : Fin (n+1) → Primal dx) (V : Fin (n+1) → Dual dy) :
    Continuous (idealHardPotential lam q c U V) := by
  have hp : Continuous (primalBlock (dx := dx) (dy := dy)) :=
    (primalProjection dx dy).continuous.congr (fun z => primal_projection_apply z)
  have hd : Continuous (dualBlock (dx := dx) (dy := dy)) :=
    (dualProjection dx dy).continuous.congr (fun z => dual_projection_apply z)
  have ha (i : Fin (n+1)) : Continuous (pairedA U V i) := (pairedA U V i).continuous
  have hb (i : Fin (n+1)) : Continuous (pairedB U V i) := (pairedB U V i).continuous
  unfold idealHardPotential idealScalarValue witnessBase
  fun_prop

/-- Entire source lemma `lem:idealgap`: the concrete feasible comparison points
have exactly the claimed gain and hence bound the genuine compact-domain gap. -/
theorem ideal_gap_witness_source {n dx dy : ℕ} (lam q c s : ℝ)
    {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)
    (X : Set (Primal dx)) (Y : Set (Dual dy)) (hX : IsCompact X) (hY : IsCompact Y)
    (x : Primal dx) (y : Dual dy)
    (hs : s = q ^ n * c - pairedA U V (Fin.last n) (joinBlocks x y))
    (hxw : x + weightWitness hU q s ∈ X) (hyw : y + weightWitness hV q s ∈ Y) :
    lam / 2 * s ^ 2 ≤ auditedSaddleGap X Y (fun u v => idealHardPotential lam q c U V (joinBlocks u v)) x y ∧
    idealHardPotential lam q c U V (joinBlocks x (y + weightWitness hV q s)) -
      idealHardPotential lam q c U V (joinBlocks (x + weightWitness hU q s) y) = lam / 2 * s ^ 2 := by
  have he := idealHardPotential_witness_exact lam q c s hU hV x y hs
  have hb := saddle_differences_bddAbove_of_compact
    (fun u v => idealHardPotential lam q c U V (joinBlocks u v))
    hX hY ⟨x + weightWitness hU q s, hxw⟩ ⟨y + weightWitness hV q s, hyw⟩ x y
    ((idealHardPotential_continuous lam q c U V).comp (continuous_join_primal y)).continuousOn
    ((idealHardPotential_continuous lam q c U V).comp (continuous_join_dual x)).continuousOn
  exact ⟨by rw [← he]; exact comparison_le_saddleGap hb hxw hyw, he⟩

end MinimaxAudit
