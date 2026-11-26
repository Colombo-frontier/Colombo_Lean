import FullJet.RadialDerivatives
import FullJet.GateDerivatives
import FullJet.LocalLink
import Mathlib.Analysis.NormedSpace.OperatorNorm.Prod

open scoped ContDiff BigOperators
open Function

namespace FullJet

noncomputable def derivativeEnvelope (A : ℕ → ℝ) (k : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (k + 1), A j

theorem derivativeEnvelope_ge_one (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (k : ℕ) :
    1 ≤ derivativeEnvelope A k := by
  unfold derivativeEnvelope
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (k + 1)) => hA j)
  linarith

theorem le_derivativeEnvelope (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (k j : ℕ) (hj : j ≤ k) :
    A j ≤ derivativeEnvelope A k := by
  have h := Finset.single_le_sum (s := Finset.range (k + 1)) (f := A)
    (fun j hj => hA j) (Finset.mem_range.mpr (by omega : j < k + 1))
  unfold derivativeEnvelope
  linarith

noncomputable def gateAlignmentBound (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * derivativeEnvelope gateDerivativeBound k *
    (derivativeEnvelope radialDerivativeBound k) ^ k

theorem gateAlignmentBound_nonneg (k : ℕ) : 0 ≤ gateAlignmentBound k := by
  have hG := derivativeEnvelope_ge_one gateDerivativeBound
    (fun j => le_trans zero_le_one (gateDerivativeBound_ge_one j)) k
  have hR := derivativeEnvelope_ge_one radialDerivativeBound radialDerivativeBound_nonneg k
  unfold gateAlignmentBound
  positivity

section Contraction
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_comp_contraction {f : F → G} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by
    exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))]
  have h := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  have hp : (∏ _i : Fin k, ‖L‖) ≤ 1 := by
    simpa using (pow_le_one₀ (norm_nonneg L) hL : ‖L‖ ^ k ≤ 1)
  exact h.trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _))

end Contraction

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem alignment_contDiff (θ : E) : ContDiff ℝ ∞ (alignment θ) :=
  (innerSL ℝ θ).contDiff.comp radial_contDiff

theorem alignment_projection_derivative_bound {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (θ : E) (hθ : ‖θ‖ ≤ 1)
    (L : F →L[ℝ] E) (hL : ‖L‖ ≤ 1) (k : ℕ) (x : F) :
    ‖iteratedFDeriv ℝ k (alignment θ ∘ L) x‖ ≤ radialDerivativeBound k := by
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (alignment θ) (L x)‖ :=
      norm_iteratedFDeriv_comp_contraction (alignment_contDiff θ) L hL k x
    _ ≤ ‖θ‖ * radialDerivativeBound k := alignment_derivative_bound θ (L x) k
    _ ≤ radialDerivativeBound k := mul_le_of_le_one_left (radialDerivativeBound_nonneg k) hθ

noncomputable def gateAlignment (θ : E) (z : E × E) : ℝ :=
  gate (5 / 32) (9 / 32) (alignment θ z.1)

theorem gateAlignment_contDiff (θ : E) : ContDiff ℝ ∞ (gateAlignment θ) :=
  (gate_contDiff _ _).comp ((alignment_contDiff θ).comp contDiff_fst)

theorem gateAlignment_derivative_bound (θ : E) (hθ : ‖θ‖ ≤ 1) (k : ℕ) (x : E × E) :
    ‖iteratedFDeriv ℝ k (gateAlignment θ) x‖ ≤ gateAlignmentBound k := by
  have hG0 j : 0 ≤ gateDerivativeBound j := le_trans zero_le_one (gateDerivativeBound_ge_one j)
  have hR1 := derivativeEnvelope_ge_one radialDerivativeBound radialDerivativeBound_nonneg k
  apply norm_iteratedFDeriv_comp_le (gate_contDiff _ _)
    ((alignment_contDiff θ).comp contDiff_fst) (by
      exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)) x
  · intro j hj
    exact (explicit_gate_derivative_bound j _).trans
      (le_derivativeEnvelope gateDerivativeBound hG0 k j hj)
  · intro j hj hjk
    calc
      _ ≤ radialDerivativeBound j := alignment_projection_derivative_bound θ hθ
        (ContinuousLinearMap.fst ℝ E E) (ContinuousLinearMap.norm_fst_le ℝ E E) j x
      _ ≤ derivativeEnvelope radialDerivativeBound k :=
        le_derivativeEnvelope radialDerivativeBound radialDerivativeBound_nonneg k j hjk
      _ ≤ _ := le_self_pow₀ hR1 (by omega)

noncomputable def rowFactor (s : E) (ρ : ℝ) (z : E × E) : ℝ :=
  ρ⁻¹ * alignment s z.2 + 1

theorem rowFactor_contDiff (s : E) (ρ : ℝ) : ContDiff ℝ ∞ (rowFactor s ρ) :=
  (contDiff_const.mul ((alignment_contDiff s).comp contDiff_snd)).add contDiff_const

theorem rowFactor_derivative_bound (s : E) (hs : ‖s‖ ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (k : ℕ) (x : E × E) :
    ‖iteratedFDeriv ℝ k (rowFactor s ρ) x‖ ≤ (radialDerivativeBound k + 1) / ρ := by
  have ha : ContDiff ℝ k (fun z : E × E => alignment s z.2) :=
    ((alignment_contDiff s).comp contDiff_snd).of_le (by
      exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  have hb := alignment_projection_derivative_bound s hs
    (ContinuousLinearMap.snd ℝ E E) (ContinuousLinearMap.norm_snd_le ℝ E E) k x
  have hconst : ‖iteratedFDeriv ℝ k (fun _ : E × E => (1 : ℝ)) x‖ ≤ 1 := by
    cases k with
    | zero => simp [norm_iteratedFDeriv_zero]
    | succ k => simp [iteratedFDeriv_succ_const]
  unfold rowFactor
  rw [iteratedFDeriv_add_apply' (contDiffAt_const.mul ha.contDiffAt) contDiffAt_const]
  have heq : (fun z : E × E => ρ⁻¹ * alignment s z.2) =
      fun z => ρ⁻¹ • alignment s z.2 := rfl
  rw [heq, iteratedFDeriv_const_smul_apply' (a := ρ⁻¹) ha.contDiffAt]
  calc
    _ ≤ ‖ρ⁻¹ • iteratedFDeriv ℝ k (fun z : E × E => alignment s z.2) x‖ + 1 :=
      (norm_add_le _ _).trans (add_le_add_left hconst _)
    _ ≤ ρ⁻¹ * radialDerivativeBound k + 1 := by
      have hnsmul := norm_smul (ρ⁻¹) (iteratedFDeriv ℝ k (fun z : E × E => alignment s z.2) x)
      rw [hnsmul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hρ.le)) _
    _ ≤ (radialDerivativeBound k + 1) / ρ := by
      apply (le_div_iff₀ hρ).mpr
      calc
        _ = radialDerivativeBound k + ρ := by field_simp
        _ ≤ radialDerivativeBound k + 1 := add_le_add_left hρ1 _

noncomputable def concreteLink (θ s : E) (ρ : ℝ) (z : E × E) : ℝ :=
  gateAlignment θ z * rowFactor s ρ z

theorem concreteLink_contDiff (θ s : E) (ρ : ℝ) : ContDiff ℝ ∞ (concreteLink θ s ρ) :=
  (gateAlignment_contDiff θ).mul (rowFactor_contDiff s ρ)

noncomputable def localLinkBound (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * derivativeEnvelope gateAlignmentBound k *
    (derivativeEnvelope radialDerivativeBound k + 1)

theorem localLinkBound_nonneg (k : ℕ) : 0 ≤ localLinkBound k := by
  have hU := derivativeEnvelope_ge_one gateAlignmentBound gateAlignmentBound_nonneg k
  have hR := derivativeEnvelope_ge_one radialDerivativeBound radialDerivativeBound_nonneg k
  unfold localLinkBound
  positivity

/-- The concrete link of the manuscript has order-k norm at most `L_k / ρ`.
Every premise now concerns construction parameters, with no derivative bound
left as an unproved hypothesis. -/
theorem concreteLink_derivative_bound (θ s : E) (hθ : ‖θ‖ ≤ 1) (hs : ‖s‖ ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (k : ℕ) (x : E × E) :
    ‖iteratedFDeriv ℝ k (concreteLink θ s ρ) x‖ ≤ localLinkBound k / ρ := by
  apply local_link_norm_bound k x (derivativeEnvelope gateAlignmentBound k)
    (derivativeEnvelope radialDerivativeBound k + 1) ρ
    (gateAlignment_contDiff θ) (rowFactor_contDiff s ρ)
    (le_trans zero_le_one (derivativeEnvelope_ge_one _ gateAlignmentBound_nonneg k))
    (by have := derivativeEnvelope_ge_one _ radialDerivativeBound_nonneg k; linarith) hρ
  · intro r hr
    exact (gateAlignment_derivative_bound θ hθ r x).trans
      (le_derivativeEnvelope _ gateAlignmentBound_nonneg k r hr)
  · intro r hr
    exact (rowFactor_derivative_bound s hs ρ hρ hρ1 r x).trans
      (div_le_div_of_nonneg_right (add_le_add_right
        (le_derivativeEnvelope _ radialDerivativeBound_nonneg k r hr) 1) hρ.le)

/-- The full directional local-link estimate with the two block norms. -/
theorem concreteLink_derivative_apply_bound (θ s : E) (hθ : ‖θ‖ ≤ 1) (hs : ‖s‖ ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (k : ℕ) (x : E × E)
    (h : Fin k → E × E) :
    |iteratedFDeriv ℝ k (concreteLink θ s ρ) x h| ≤
      (localLinkBound k / ρ) * ∏ l, (‖(h l).1‖ + ‖(h l).2‖) := by
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (concreteLink θ s ρ) x‖ * ∏ l, ‖h l‖ :=
      (iteratedFDeriv ℝ k (concreteLink θ s ρ) x).le_opNorm h
    _ ≤ _ := mul_le_mul
      (concreteLink_derivative_bound θ s hθ hs ρ hρ hρ1 k x)
      (Finset.prod_le_prod (fun l hl => norm_nonneg _) (fun l hl => by
        rw [Prod.norm_def]
        exact max_le (le_add_of_nonneg_right (norm_nonneg _))
          (le_add_of_nonneg_left (norm_nonneg _))))
      (Finset.prod_nonneg (fun l hl => norm_nonneg _))
      (div_nonneg (localLinkBound_nonneg k) hρ.le)

end Inner

end FullJet
