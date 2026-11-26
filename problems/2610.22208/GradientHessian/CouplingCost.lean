import GradientHessian.ScaledJets
import GradientHessian.HigherHierarchyFunctions

/-! Actual full-space derivatives of the eight incoming-coupling terms.
The fixed constants do not depend on dimension, height, or descendant count. -/

noncomputable section
namespace GradientHessian.CouplingCost
open ScaledJets HigherHierarchy LocalizedProductDerivatives
open scoped BigOperators

def profileConstant : ℝ := 768 + localizedConstant + LatchLemma.latchConstant
theorem profileConstant_pos : 0 < profileConstant := by
  have hL := localizedConstant_pos
  have hC := LatchLemma.latchConstant_pos
  unfold profileConstant
  linarith
theorem profileConstant_bounds : 768 ≤ profileConstant ∧ localizedConstant ≤ profileConstant ∧
    LatchLemma.latchConstant ≤ profileConstant := by
  have hL := localizedConstant_pos
  have hC := LatchLemma.latchConstant_pos
  unfold profileConstant
  constructor
  · linarith
  constructor <;> linarith

def weightConstant : ℝ := 8 * (1 + profileConstant) * (8 * profileConstant)^8
def termConstant : ℝ := 8 * (8 * (64 * weightConstant) * (64 * profileConstant)) * profileConstant
def couplingConstant : ℝ := 8 * termConstant

theorem weightConstant_pos : 0 < weightConstant := by
  have h := profileConstant_pos
  unfold weightConstant
  positivity
theorem termConstant_pos : 0 < termConstant := by
  have h := profileConstant_pos
  have hW := weightConstant_pos
  unfold termConstant
  positivity
theorem couplingConstant_pos : 0 < couplingConstant := mul_pos (by norm_num) termConstant_pos

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem port_scaledJets {w : ℝ} (hw : 0 < w) (c : E) :
    Bound (Localized.port w c) profileConstant w := by
  refine ⟨profileConstant_pos.le, (Localized.localized_contDiff hw hw c).2.2, ?_⟩
  intro n hn x
  apply (LocalizedHigherDerivatives.port_higher_derivative_bound hw n hn c x).trans
  exact div_le_div_of_nonneg_right
    ((localizedConstant_bounds hn).2.trans profileConstant_bounds.2.1) (pow_nonneg hw.le n)

theorem nodePort_scaledJets {w : ℝ} (hw : 0 < w) (c : Fin 8 → E) (i : Fin 8) :
    Bound (fun Z : Layer F E => nodePorts w c Z i) profileConstant w :=
  (port_scaledJets hw (c i)).comp_linear (parentAt F E i) (parentAt_norm_le F E i)

theorem weight_scaledJets {w : ℝ} (hw : 0 < w) (c : Fin 8 → E) (i : Fin 8) :
    Bound (fun Z : Layer F E => InnerSelector.weight (nodePorts w c Z) i) weightConstant w := by
  have hfirst := (constant (F := Layer F E) hw (c := 1) (C := 1) (by norm_num)).sub
    (nodePort_scaledJets (F := F) hw c i) hw
  have hp := finset_prod (Finset.univ : Finset (Fin 8))
    (fun (j : Fin 8) (Z : Layer F E) => if j < i then nodePorts w c Z j else 1) hw (C := profileConstant)
    (by
      intro j _
      by_cases h : j < i
      · simpa only [if_pos h] using nodePort_scaledJets (F := F) hw c j
      · simpa only [if_neg h] using (constant (F := Layer F E) hw (c := 1)
          (C := profileConstant) (by have hC := profileConstant_bounds.1; norm_num; linarith)))
  simpa only [InnerSelector.weight, Finset.card_univ, Fintype.card_fin, weightConstant] using hfirst.mul hp hw

variable [CompleteSpace E]

theorem incoming_scaledJets {R w : ℝ} (hw : 0 < w) (hs : 16*w ≤ R)
    (c : E) (hc : ‖c‖ = R) : Bound (Localized.incoming R w c) (profileConstant*R) w := by
  have hwR : w ≤ R := by linarith
  have hR : 0 < R := hw.trans_le hwR
  have h := localized_bounds hw hs c hc
  refine ⟨mul_nonneg profileConstant_pos.le hR.le, h.smooth_incoming, ?_⟩
  intro n hn x
  by_cases hn0 : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (by linarith [(h.incoming_values x).1]),
      pow_zero, div_one]
    exact (h.incoming_values x).2.trans (mul_le_mul_of_nonneg_right profileConstant_bounds.1 hR.le)
  · have hi := h.incoming_derivatives n (by omega) hn x
    rw [zpow_sub₀ hw.ne', zpow_one, zpow_natCast] at hi
    apply hi.trans
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul profileConstant_bounds.2.1 hwR hw.le profileConstant_pos.le) (pow_nonneg hw.le n)

theorem nodeIncoming_scaledJets {R w : ℝ} (hw : 0 < w) (hs : 16*w ≤ R)
    (c : Fin 8 → E) (hc : ∀ i, ‖c i‖ = R) (i : Fin 8) :
    Bound (fun Z : Layer F E => nodeIncoming R w c Z i) (profileConstant*R) w :=
  (incoming_scaledJets hw hs (c i) (hc i)).comp_linear (parentAt F E i) (parentAt_norm_le F E i)

def term (R w : ℝ) (c : Fin 8 → E) (o : Fin 8 → F → ℝ) (i : Fin 8) (Z : Layer F E) : ℝ :=
  InnerSelector.weight (nodePorts w c Z) i * nodeIncoming R w c Z i * o i (lower F E Z)

def coupling (R w : ℝ) (c : Fin 8 → E) (o : Fin 8 → F → ℝ) (Z : Layer F E) : ℝ :=
  ∑ i, term R w c o i Z

theorem term_scaledJets {R w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (hs : 16*w ≤ R) (hbw : b ≤ 4*w) (c : Fin 8 → E) (hc : ∀ i, ‖c i‖ = R)
    (o : Fin 8 → F → ℝ) (ho : ∀ i, Bound (o i) profileConstant b) (i : Fin 8) :
    Bound (term R w c o i) (termConstant*R) b := by
  have hW := (weight_scaledJets (F := F) hw c i).changeScale hw hb hbw
  have hB := (nodeIncoming_scaledJets (F := F) hw hs c hc i).changeScale hw hb hbw
  have hO := (ho i).comp_linear (lower F E) (lower_norm_le F E)
  convert (hW.mul hB hb).mul hO hb using 1
  unfold termConstant
  ring

theorem coupling_scaledJets {R w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (hs : 16*w ≤ R) (hbw : b ≤ 4*w) (c : Fin 8 → E) (hc : ∀ i, ‖c i‖ = R)
    (o : Fin 8 → F → ℝ) (ho : ∀ i, Bound (o i) profileConstant b) :
    Bound (coupling R w c o) (couplingConstant*R) b := by
  have hR : 0 < R := by linarith
  have h := finset_sum (Finset.univ : Finset (Fin 8)) (term R w c o) hb
    (mul_nonneg termConstant_pos.le hR.le)
    (fun i _ => term_scaledJets hw hb hs hbw c hc o ho i)
  simpa only [coupling, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat, couplingConstant,
    mul_assoc] using h

theorem perturbation_scaledJets {R w : ℝ} (hw : 0 < w) (hwR : w ≤ R) (c : E) :
    Bound (Localized.perturbation R w c) (profileConstant*w) w := by
  refine ⟨mul_nonneg profileConstant_pos.le hw.le, perturbation_contDiff (hw.trans_le hwR) w c, ?_⟩
  intro n hn x
  have hp := perturbation_derivative_bound hw hwR hn c x
  rw [zpow_sub₀ hw.ne', zpow_one, zpow_natCast, ← mul_div_assoc] at hp
  apply hp.trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hw.le n)
  apply mul_le_mul_of_nonneg_right _ hw.le
  have hc := (localizedConstant_bounds hn).1
  linarith [profileConstant_bounds.2.1]

theorem nodePerturbation_scaledJets {R w : ℝ} (hw : 0 < w) (hwR : w ≤ R) (c : Fin 8 → E) :
    Bound (nodePerturbation R w c : Layer F E → ℝ) ((8*profileConstant)*w) w := by
  have h := finset_sum (Finset.univ : Finset (Fin 8))
    (fun (i : Fin 8) (Z : Layer F E) => Localized.perturbation R w (c i) (parentAt F E i Z)) hw
    (mul_nonneg profileConstant_pos.le hw.le)
    (fun i _ => (perturbation_scaledJets hw hwR (c i)).comp_linear
      (parentAt F E i) (parentAt_norm_le F E i))
  simpa only [nodePerturbation, parentAt_apply, Finset.card_univ, Fintype.card_fin,
    Nat.cast_ofNat, mul_assoc] using h

end GradientHessian.CouplingCost

