import GradientHessian.FirstHeightLeafData
import GradientHessian.LeafCoercivity
import GradientHessian.LocalizedBounds

/-! Quantitative coercivity of the actual shared physical baseline. A new
height appends only its own parent blocks; sibling parameters add no blocks. -/

noncomputable section
namespace GradientHessian.HierarchyCoercivity
open InnerCoordinates EuclideanRegisters Filter Bornology
open scoped BigOperators

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem registers_norm_le_sum {n : ℕ} (U : Registers E n) :
    ‖U‖ ≤ ∑ i, ‖U i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg (U i))).1
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (U i))

omit [InnerProductSpace ℝ F] [InnerProductSpace ℝ E] in
theorem layer_norm_le {n : ℕ} (Z : WithLp 2 (F × Registers E n)) :
    ‖Z‖ ≤ ‖Z.fst‖ + ∑ i, ‖Z.snd i‖ := by
  have hs := registers_norm_le_sum Z.snd
  have hn : 0 ≤ ∑ i, ‖Z.snd i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hp := WithLp.prod_norm_sq_eq_of_L2 Z
  have hs2 := mul_self_le_mul_self (norm_nonneg Z.snd) hs
  nlinarith [norm_nonneg Z, norm_nonneg Z.fst,
    mul_nonneg (norm_nonneg Z.fst) hn]

def extension {n : ℕ} (Q : F → ℝ) (R : ℝ)
    (Z : WithLp 2 (F × Registers E n)) : ℝ :=
  Q Z.fst + ∑ i, Localized.publicPotential R (Z.snd i)

omit [InnerProductSpace ℝ F] [InnerProductSpace ℝ E] in
theorem extension_linear_lower {n : ℕ} (Q : F → ℝ) (R c C : ℝ)
    (hc : 0 ≤ c) (hc16 : c ≤ 16) (hQ : ∀ x, c * ‖x‖ - C ≤ Q x)
    (Z : WithLp 2 (F × Registers E n)) :
    c * ‖Z‖ - (C + 16 * n * R) ≤ extension Q R Z := by
  have hsum : (∑ i : Fin n, (c * ‖Z.snd i‖ - 16 * R)) ≤
      ∑ i : Fin n, Localized.publicPotential R (Z.snd i) := by
    apply Finset.sum_le_sum
    intro i _
    have h := Localized.publicPotential_lower R (Z.snd i)
    have hm := mul_le_mul_of_nonneg_right hc16 (norm_nonneg (Z.snd i))
    linarith
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn := mul_le_mul_of_nonneg_left (layer_norm_le Z) hc
  have hb := hQ Z.fst
  unfold extension
  nlinarith

omit [InnerProductSpace ℝ F] in
theorem coercive_of_linear_lower {Q : F → ℝ} {c C : ℝ}
    (hc : 0 < c) (hQ : ∀ x, c * ‖x‖ - C ≤ Q x) :
    Tendsto Q (cobounded F) atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_cobounded_le_norm (E := F) ((b + C) / c)] with x hx
  have hm := (div_le_iff₀ hc).1 hx
  have h := hQ x
  nlinarith

omit [InnerProductSpace ℝ F] in
theorem quadratic_to_linear {Q : F → ℝ} {c C : ℝ}
    (hc : 0 ≤ c) (hQ : ∀ x, c * ‖x‖ ^ 2 - C ≤ Q x) (x : F) :
    c * ‖x‖ - (C + c) ≤ Q x := by
  have hsq : ‖x‖ ≤ ‖x‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hm := mul_le_mul_of_nonneg_left hsq hc
  have h := hQ x
  nlinarith

omit [InnerProductSpace ℝ F] [InnerProductSpace ℝ E] in
theorem extension_coercive {n : ℕ} (Q : F → ℝ) (R c C : ℝ)
    (hc : 0 < c) (hc16 : c ≤ 16) (hQ : ∀ x, c * ‖x‖ - C ≤ Q x) :
    Tendsto (extension (E := E) (n := n) Q R) (cobounded _) atTop :=
  coercive_of_linear_lower hc (extension_linear_lower Q R c C hc.le hc16 hQ)

theorem public_memory_quadratic_lower {m k : ℕ} (Z : InnerCoordinates.Space F E m (k+2)) :
    (4 / Inner.lastRadius k) * ‖tasks F E m (k+2) Z‖^2 ≤ Inner.publicQuadratic m k Z := by
  have hcoef (j : Fin (k+2)) : 4 / Inner.lastRadius k ≤ 4 / Inner.radius k j :=
    div_le_div_of_nonneg_left (by norm_num) (Inner.radius_pos _ j) (Leaf.inner_radius_le_last _ j)
  calc
    _ = ∑ i, ∑ j, (4 / Inner.lastRadius k) * ‖tasks F E m (k+2) Z i j‖^2 := by
      rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    _ ≤ _ := by
      unfold Inner.publicQuadratic LatchChain.publicQuadratic
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hcoef j) (sq_nonneg _)

def firstCoefficient (m : ℕ) : ℝ :=
  min Leaf.coercivityConstant (4 / FirstHeight.outerRadius (m+1))

theorem firstCoefficient_pos (m : ℕ) : 0 < firstCoefficient m := by
  apply lt_min Leaf.coercivityConstant_pos
  unfold FirstHeight.outerRadius Inner.lastRadius
  positivity

theorem firstCoefficient_le_half (m : ℕ) : firstCoefficient m ≤ 1/2 :=
  (min_le_left _ _).trans Leaf.coercivityConstant_le_half

def firstEnergy (m : ℕ) (Z : FirstHeight.SourceSpace F E m) : ℝ :=
  let z := numerical (Leaf.Space F E (m+1)) E 8 (FirstHeight.depth (m+1)+2) Z
  ‖numerical F E (m+1) (Inner.absoluteDepth+2) z‖^2/2 +
    Inner.publicQuadratic (m+1) Inner.absoluteDepth z +
    Inner.publicQuadratic 8 (FirstHeight.depth (m+1)) Z

theorem firstEnergy_quadratic_lower (m : ℕ) (Z : FirstHeight.SourceSpace F E m) :
    firstCoefficient m * ‖Z‖^2 ≤ firstEnergy m Z := by
  let z := numerical (Leaf.Space F E (m+1)) E 8 (FirstHeight.depth (m+1)+2) Z
  have hinner := Leaf.public_memory_lower z
  have houter := public_memory_quadratic_lower Z
  have hi := mul_le_mul_of_nonneg_right
    (show firstCoefficient m ≤ Leaf.coercivityConstant from min_le_left _ _)
    (sq_nonneg ‖tasks F E (m+1) (Inner.absoluteDepth+2) z‖)
  have ho := mul_le_mul_of_nonneg_right
    (show firstCoefficient m ≤ 4 / Inner.lastRadius (FirstHeight.depth (m+1)) from min_le_right _ _)
    (sq_nonneg ‖tasks (Leaf.Space F E (m+1)) E 8 (FirstHeight.depth (m+1)+2) Z‖)
  have hy := mul_le_mul_of_nonneg_right (firstCoefficient_le_half m)
    (sq_nonneg ‖numerical F E (m+1) (Inner.absoluteDepth+2) z‖)
  have hn : ‖Z‖^2 = ‖z‖^2 +
      ‖tasks (Leaf.Space F E (m+1)) E 8 (FirstHeight.depth (m+1)+2) Z‖^2 :=
    WithLp.prod_norm_sq_eq_of_L2 Z
  rw [Leaf.physical_norm_square z] at hn
  change firstCoefficient m * ‖Z‖^2 ≤
    ‖numerical F E (m+1) (Inner.absoluteDepth+2) z‖^2/2 +
      Inner.publicQuadratic (m+1) Inner.absoluteDepth z +
      Inner.publicQuadratic 8 (FirstHeight.depth (m+1)) Z
  rw [hn, mul_add, mul_add]
  linarith

theorem firstEnergy_linear_lower (m : ℕ) (Z : FirstHeight.SourceSpace F E m) :
    firstCoefficient m * ‖Z‖ - firstCoefficient m ≤ firstEnergy m Z := by
  simpa using quadratic_to_linear (C := 0) (firstCoefficient_pos m).le
    (fun Z => by simpa using firstEnergy_quadratic_lower m Z) Z

theorem first_node_quadratic_lower (d : FirstHeight.Data F E m)
    (hA : ∀ i, InverseGate.LowerBound (d.A i)) (Z : FirstHeight.SourceSpace F E m) :
    firstCoefficient m * ‖Z‖^2 - FirstHeight.firstAmplitude m - Inner.innerConstant*(m+1) ≤
      FirstHeight.sourceNode d Z := by
  have h := FirstHeight.sourceNode_energy d hA Z
  have hq := firstEnergy_quadratic_lower m Z
  change firstEnergy m Z - FirstHeight.firstAmplitude m - Inner.innerConstant*(m+1) ≤ _ at h
  linarith

theorem first_node_coercive (d : FirstHeight.Data F E m)
    (hA : ∀ i, InverseGate.LowerBound (d.A i)) :
    Tendsto (FirstHeight.sourceNode d) (cobounded _) atTop := by
  have hq : ∀ Z, firstCoefficient m * ‖Z‖^2 -
      (FirstHeight.firstAmplitude m + Inner.innerConstant*(m+1)) ≤
        FirstHeight.sourceNode d Z := by
    intro Z
    have h := first_node_quadratic_lower d hA Z
    linarith
  exact coercive_of_linear_lower (firstCoefficient_pos m)
    (quadratic_to_linear (firstCoefficient_pos m).le hq)

end GradientHessian.HierarchyCoercivity
