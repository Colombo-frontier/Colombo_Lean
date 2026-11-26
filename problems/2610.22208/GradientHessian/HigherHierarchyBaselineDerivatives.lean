import GradientHessian.HigherHierarchyFunctions
import GradientHessian.LeafRegularity
import GradientHessian.LocalizedNormDerivatives

/-! Uniform actual third derivatives of the common public baseline.
The first baseline is quadratic; later contributions form a geometric sum. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u
open InnerCoordinates

section Quadratic
variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_publicQuadratic_third_zero (m k : ℕ) (Z : InnerCoordinates.Space Y E m (k+2)) :
    iteratedFDeriv ℝ 3 (Inner.publicQuadratic m k) Z = 0 := by
  let f := fun (i : Fin m) (j : Fin (k+2)) (W : InnerCoordinates.Space Y E m (k+2)) =>
    (4/Inner.radius k j)*‖tasks Y E m (k+2) W i j‖^2
  have hf (i : Fin m) (j : Fin (k+2)) : ContDiff ℝ 3 (f i j) :=
    contDiff_const.mul (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k+2) => E) j).contDiff.comp
      (Inner.taskProjection (Y := Y) (E := E) m k i).contDiff).norm_sq ℝ)
  change iteratedFDeriv ℝ 3 (fun W => ∑ i, ∑ j, f i j W) Z = 0
  rw [iteratedFDeriv_sum (f := fun i W => ∑ j, f i j W)
    (fun i _ => ContDiff.sum (fun j _ => hf i j))]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [iteratedFDeriv_sum (fun j _ => hf i j)]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  exact Leaf.weighted_square_third_zero _
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k+2) => E) j).comp
      (Inner.taskProjection (Y := Y) (E := E) m k i)) Z

theorem firstBaseline_third_zero (m : ℕ) (Z : FirstHeight.SourceSpace Y E m) :
    iteratedFDeriv ℝ 3 (FirstHeight.sourceBaseline m) Z = 0 := by
  let N := numerical (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2)
  have hN : ContDiff ℝ 3 (fun W => Leaf.publicQuadratic (m+1) (N W)) :=
    (Leaf.publicQuadratic_contDiff _).comp N.contDiff
  have h0 : iteratedFDeriv ℝ 3 (fun W => Leaf.publicQuadratic (m+1) (N W)) Z = 0 := by
    have hh := Inner.derivative_comp_linear_le N (Inner.numerical_norm_le _ _)
      (Leaf.publicQuadratic_contDiff (m+1)) (n := 3) le_rfl Z
    rw [Leaf.publicQuadratic_third_zero, norm_zero] at hh
    exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
  change iteratedFDeriv ℝ 3 (fun W => Leaf.publicQuadratic (m+1) (N W)+
    Inner.publicQuadratic 8 (FirstHeight.depth (m+1)) W) Z = 0
  rw [iteratedFDeriv_add_apply' hN.contDiffAt (Inner.publicQuadratic_contDiff _ _).contDiffAt,
    h0, inner_publicQuadratic_third_zero, add_zero]
end Quadratic

section Layer
variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem parentPublic_third_bound {R : ℝ} (hR : 0 < R) (Z : Layer F E) :
    ‖iteratedFDeriv ℝ 3 (fun W : Layer F E => ∑ i, Localized.publicPotential R (parent F E W i)) Z‖ ≤
      384/R^2 := by
  have hf (i : Fin 8) : ContDiff ℝ 3 (fun W : Layer F E => Localized.publicPotential R (parent F E W i)) :=
    (Localized.publicPotential_contDiff hR 3).comp (parentAt F E i).contDiff
  rw [iteratedFDeriv_sum (fun i _ => hf i)]
  simp only [Finset.sum_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 8, 48/R^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hc := Inner.derivative_comp_linear_le (parentAt F E i) (parentAt_norm_le F E i)
        (Localized.publicPotential_contDiff hR 3) (n := 3) le_rfl Z
      apply hc.trans
      have hp := LocalizedNormDerivatives.publicPotential_derivative_bound hR
        (n := 3) (by norm_num) le_rfl (parent F E Z i)
      exact hp
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem nodeBaseline_third_le (Q : F → ℝ) {R : ℝ} (hR : 0 < R) (hQ : ContDiff ℝ 3 Q) (Z : Layer F E) :
    ‖iteratedFDeriv ℝ 3 (nodeBaseline Q R) Z‖ ≤
      ‖iteratedFDeriv ℝ 3 Q (lower F E Z)‖ + 384/R^2 := by
  have hp : ContDiff ℝ 3 (fun W : Layer F E => ∑ i, Localized.publicPotential R (parent F E W i)) :=
    ContDiff.sum (fun i _ => (Localized.publicPotential_contDiff hR 3).comp (parentAt F E i).contDiff)
  have h := Inner.norm_iteratedFDeriv_add_le (hQ.comp (lower F E).contDiff) hp (n := 3) le_rfl Z
  exact h.trans (add_le_add (Inner.derivative_comp_linear_le (lower F E) (lower_norm_le F E) hQ le_rfl Z)
    (parentPublic_third_bound hR Z))
end Layer

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

theorem baseline_third_sum {K : ℝ} (hK : 0 < K) : ∀ t (Z : Space Y E H m t),
    ‖iteratedFDeriv ℝ 3 (baseline K t) Z‖ ≤ ∑ j ∈ Finset.range t, 384/(radius m K j)^2 := by
  intro t
  induction t with
  | zero =>
    intro Z
    simpa only [norm_zero] using (congrArg norm (firstBaseline_third_zero (Y := Y) (E := E) m Z)).le
  | succ t ih =>
    intro Z
    have h := nodeBaseline_third_le (baseline K t) (radius_pos m hK t) (baseline_contDiff hK t) Z
    have hb := h.trans (add_le_add_right (ih (lower _ _ Z)) _)
    simpa only [baseline, Finset.sum_range_succ] using hb

theorem public_radius_cost_le {K : ℝ} (hK : 1 ≤ K) (m j : ℕ) :
    384/(radius m K j)^2 ≤ 384*(1/36:ℝ)^j := by
  have hr0 : 1 ≤ FirstHeight.baseRadius (m+1) :=
    (show (1:ℝ) ≤ m+1 by exact_mod_cast (show 1 ≤ m+1 by omega)).trans (by
      simpa only [Nat.cast_add, Nat.cast_one] using (FirstHeight.baseRadius_range (M := m+1) (by omega)).1)
  have hr : (6:ℝ)^j ≤ radius m K j := by
    have hk := mul_le_mul hK hr0 (by norm_num : (0:ℝ)≤1) (by linarith : 0≤K)
    have hp := mul_le_mul_of_nonneg_right hk (by positivity : (0:ℝ)≤6^j)
    simpa only [one_mul, radius] using hp
  have hs : ((6:ℝ)^j)^2 ≤ (radius m K j)^2 := pow_le_pow_left₀ (by positivity) hr 2
  have hd := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤384) (by positivity : (0:ℝ)<((6:ℝ)^j)^2) hs
  have he : ((6:ℝ)^j)^2=(36:ℝ)^j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  apply hd.trans_eq
  rw [he, div_pow, one_pow]
  ring

/-- An absolute bound valid at every finite height and every physical
dimension. The source's K≥384 is stronger than the K≥1 used here. -/
theorem baseline_third_bound {K : ℝ} (hK : 1 ≤ K) (t : ℕ) (Z : Space Y E H m t) :
    ‖iteratedFDeriv ℝ 3 (baseline K t) Z‖ ≤ 768 := by
  apply (baseline_third_sum (by linarith : 0 < K) t Z).trans
  calc
    _ ≤ ∑ j ∈ Finset.range t, 384*(1/36:ℝ)^j := Finset.sum_le_sum (fun j _ => public_radius_cost_le hK m j)
    _ = 384*∑ j ∈ Finset.range t, (1/36:ℝ)^j := (Finset.mul_sum ..).symm
    _ ≤ 768 := by
      have h := Reliability.geometric_sum_le_two (r := (1/36:ℝ)) (by norm_num) (by norm_num) t
      linarith

end GradientHessian.HigherHierarchy
