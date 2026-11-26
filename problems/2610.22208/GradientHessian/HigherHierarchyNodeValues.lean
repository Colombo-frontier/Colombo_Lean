import GradientHessian.HigherHierarchyNode

/-! Value estimates for the actual localized node. The terminal selector
charges the inherited common loss once, independently of branching. -/

noncomputable section
namespace GradientHessian.HigherHierarchy

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem nodePerturbation_bounds {R w : ℝ} (hR : 0 < R) (hw : 0 < w)
    (c : Fin 8 → E) (Z : Layer F E) :
    -8*208*w ≤ nodePerturbation R w c Z ∧ nodePerturbation R w c Z ≤ 0 := by
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (Localized.perturbation_bounds hR hw (c i) (parent F E Z i)).1)
  have hhi := Finset.sum_nonpos (s := Finset.univ) (fun i _ =>
    (Localized.perturbation_bounds hR hw (c i) (parent F E Z i)).2)
  constructor
  · norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] at hlo
    unfold nodePerturbation
    linarith
  · exact hhi

theorem nodePayload_interval (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    {A C R w : ℝ} (hw : 0 < w) (hscale : 16*w ≤ R)
    (c : Fin 8 → E) (hc : ∀ i, ‖c i‖ = R) (Z : Layer F E)
    (hf : ∀ i, -A-C ≤ child i (lower F E Z)-Q (lower F E Z) ∧
      child i (lower F E Z)-Q (lower F E Z) ≤ 0)
    (ho : ∀ i, childPort i (lower F E Z) ∈ Set.Icc (0 : ℝ) 1) (i : Fin 8) :
    -((i.val:ℝ)+1)*(A+768*R)-C ≤ nodePayload Q child childPort (A+768*R) R w c Z i ∧
    nodePayload Q child childPort (A+768*R) R w c Z i ≤ -(i.val:ℝ)*(A+768*R) := by
  have hR : 0 ≤ R := by linarith
  have hB := Localized.incoming_bounds hw hscale (c i) (parent F E Z i) (hc i)
  have hB0 : 0 ≤ nodeIncoming R w c Z i := le_trans (by positivity) hB.1
  have hprod0 := mul_nonneg hB0 (ho i).1
  have hprod := mul_le_mul hB.2 (ho i).2 (ho i).1 (by positivity : 0 ≤ 768*R)
  change nodeIncoming R w c Z i * childPort i (lower F E Z) ≤ _ at hprod
  simp only [mul_one] at hprod
  unfold nodePayload
  constructor <;> nlinarith [hf i |>.1, hf i |>.2]

theorem nodeResidual_bounds (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    {A C R w : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hw : 0 < w) (hscale : 16*w ≤ R)
    (c : Fin 8 → E) (hc : ∀ i, ‖c i‖ = R) (Z : Layer F E)
    (hf : ∀ i, -A-C ≤ child i (lower F E Z)-Q (lower F E Z) ∧
      child i (lower F E Z)-Q (lower F E Z) ≤ 0)
    (ho : ∀ i, childPort i (lower F E Z) ∈ Set.Icc (0 : ℝ) 1) :
    -(8*(A+768*R)+8*208*w)-C ≤ nodeResidual Q child childPort (A+768*R) R w c Z ∧
    nodeResidual Q child childPort (A+768*R) R w c Z ≤ 0 := by
  have hR : 0 < R := by linarith
  have hS : 0 ≤ A+768*R := by positivity
  have he := nodePayload_interval Q child childPort hw hscale c hc Z hf ho
  have hl := FirstHeightSelector.le_select 8 (nodePorts w c Z)
    (nodePayload Q child childPort (A+768*R) R w c Z) (-8*(A+768*R))
    (-8*(A+768*R)-C) (nodePorts_bounds w c Z) (fun i => by
      have hi : (i.val:ℝ)+1 ≤ 8 := by exact_mod_cast (show i.val+1 ≤ 8 from i.isLt)
      have hm := mul_le_mul_of_nonneg_right hi hS
      linarith [(he i).1]) (by linarith)
  have hu := FirstHeightSelector.select_le 8 (nodePorts w c Z)
    (nodePayload Q child childPort (A+768*R) R w c Z) (-8*(A+768*R)) 0
    (nodePorts_bounds w c Z) (fun i => by
      have hi := mul_nonneg (Nat.cast_nonneg i.val) hS
      linarith [(he i).2]) (by linarith)
  have hp := nodePerturbation_bounds hR hw c Z
  rw [nodeResidual_eq]
  change -8*(A+768*R)-C ≤ nodeSelected Q child childPort (A+768*R) R w c Z at hl
  change nodeSelected Q child childPort (A+768*R) R w c Z ≤ 0 at hu
  constructor <;> linarith

/-- The common positive lower energy is inherited once, while the child
amplitude is absorbed into the exact next spacing. -/
theorem nodeScalar_energy (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    {A C R w J : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hw : 0 < w) (hscale : 16*w ≤ R)
    (c : Fin 8 → E) (hc : ∀ i, ‖c i‖ = R) (Z : Layer F E)
    (hQ : J ≤ Q (lower F E Z))
    (hf : ∀ i, J-A-C ≤ child i (lower F E Z))
    (ho : ∀ i, childPort i (lower F E Z) ∈ Set.Icc (0 : ℝ) 1) :
    J + (∑ i, Localized.publicPotential R (parent F E Z i)) -
      (8*(A+768*R)+8*208*w)-C ≤ nodeScalar Q child childPort (A+768*R) R w c Z := by
  have hR : 0 < R := by linarith
  have hS : 0 ≤ A+768*R := by positivity
  have hl := FirstHeightSelector.le_select 8 (nodePorts w c Z)
    (nodePayload Q child childPort (A+768*R) R w c Z) (-8*(A+768*R))
    (J-Q (lower F E Z)-8*(A+768*R)-C) (nodePorts_bounds w c Z) (fun i => by
      have hB := Localized.incoming_bounds hw hscale (c i) (parent F E Z i) (hc i)
      have hprod := mul_le_mul hB.2 (ho i).2 (ho i).1 (by positivity : 0 ≤ 768*R)
      simp only [mul_one] at hprod
      have hi : (i.val:ℝ)+1 ≤ 8 := by exact_mod_cast (show i.val+1 ≤ 8 from i.isLt)
      have hm := mul_le_mul_of_nonneg_right hi hS
      unfold nodePayload nodeIncoming
      nlinarith [hf i]) (by linarith)
  have hp := (nodePerturbation_bounds hR hw c Z).1
  change J-Q (lower F E Z)-8*(A+768*R)-C ≤
    nodeSelected Q child childPort (A+768*R) R w c Z at hl
  have hr := nodeResidual_eq Q child childPort (A+768*R) R w c Z
  unfold nodeResidual nodeBaseline at hr
  linarith

end GradientHessian.HigherHierarchy
