import SecondOrder.IdealEpochEnergy

open MeasureTheory
open scoped Classical BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section

variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {η : Measure A}

theorem integral_epoch_dyadic_energy (N M L q : ℕ)
    (a m : Fin N → Fin M → A → E)
    (ha : ∀ e k, Integrable (a e k) η) (hm : ∀ e k, Integrable (m e k) η)
    (ha2 : ∀ e k, Integrable (fun w => ‖a e k w‖^2) η)
    (hm2 : ∀ e k, Integrable (fun w => ‖m e k w‖^2) η)
    (hs : ∀ e w, (Finset.univ.filter (fun k => a e k w ≠ 0)).card ≤ q)
    (ho : ∀ e i j, i ≠ j → (∫ w, ⟪m e i w,m e j w⟫_ℝ ∂η) = 0) :
    Integrable (fun w => ∑ e, ∑ i : Fin L × Fin M,
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a e k w+m e k w)‖^2) η ∧
    (∫ w, ∑ e, ∑ i : Fin L × Fin M,
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a e k w+m e k w)‖^2 ∂η) ≤
      2*(L : ℝ)*((q : ℝ)*(∫ w, ∑ e, ∑ k, ‖a e k w‖^2 ∂η)+
        (∫ w, ∑ e, ∑ k, ‖m e k w‖^2 ∂η)) := by
  have hv (e : Fin N) : Integrable (fun w => ∑ i : Fin L × Fin M,
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a e k w+m e k w)‖^2) η := by
    apply integrable_finset_sum
    intro i hi
    exact integrable_norm_sum_sq _ _ (fun k _ => (ha e k).add (hm e k))
      (fun k _ => integrable_norm_add_sq (ha e k) (hm e k) (ha2 e k) (hm2 e k))
  have hAe (e : Fin N) := integrable_finset_sum Finset.univ (fun k _ => ha2 e k)
  have hMe (e : Fin N) := integrable_finset_sum Finset.univ (fun k _ => hm2 e k)
  refine ⟨integrable_finset_sum _ (fun e _ => hv e),?_⟩
  rw [integral_finset_sum _ (fun e _ => hv e),
    integral_finset_sum _ (fun e _ => hAe e),integral_finset_sum _ (fun e _ => hMe e)]
  calc
    _ ≤ ∑ e : Fin N, 2*(L : ℝ)*((q : ℝ)*(∫ w, ∑ k, ‖a e k w‖^2 ∂η)+
        (∫ w, ∑ k, ‖m e k w‖^2 ∂η)) := by
      apply Finset.sum_le_sum
      intro e he
      exact integral_dyadic_energy M L q (a e) (m e) (ha e) (hm e) (ha2 e) (hm2 e) (hs e) (ho e)
    _ = _ := by simp only [Finset.mul_sum,Finset.sum_add_distrib,mul_add]

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {ξLaw : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ξLaw]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- All reindexed epoch dyadic blocks together have the same global energy
budget. The stochastic contribution is neither multiplied by q nor by the
number of epochs. EpochTreeEnergy connects this bound to completed chords. -/
theorem CommonLoss.idealEpoch_dyadic_energy (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M L : ℕ) :
    let a := idealEpochDrift (M := M) q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy
    let m := idealEpochInnovation (M := M) q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy
    let energy := fun w => ∑ e : Fin M, ∑ i : Fin L × Fin M,
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a (e.val,k.val) w+m (e.val,k.val) w)‖^2
    Integrable energy (ξLaw.prod (signLaw M)) ∧
      (∫ w, energy w ∂ξLaw.prod (signLaw M)) ≤
        2*(L : ℝ)*((q : ℝ)*(P.gap/P.gradientLip)+16*P.gap/(3*γ)) := by
  dsimp only
  have ha := h.idealEpochDrift_moments (η := ξLaw) hq hτ hγ hm hv M
  have hmi := h.idealEpochInnovation_moments (η := ξLaw) hq hτ hγ hm hv M
  have ho (e i j : Fin M) (hij : i ≠ j) :=
    h.idealEpochInnovation_orthogonal (η := ξLaw) hq hτ hγ hm hv M
      (e.val,i.val) (e.val,j.val) (fun he => hij (Fin.ext (congrArg Prod.snd he)))
  have he := integral_epoch_dyadic_energy M M L q
    (fun e k => idealEpochDrift q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy (e.val,k.val))
    (fun e k => idealEpochInnovation q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy (e.val,k.val))
    (fun e k => (ha (e.val,k.val)).1) (fun e k => (hmi (e.val,k.val)).1)
    (fun e k => (ha (e.val,k.val)).2) (fun e k => (hmi (e.val,k.val)).2)
    (fun e w => by
      convert idealEpochDrift_support hq P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy w e.val using 1
      congr 1
      ext k
      simp) ho
  have hb := h.idealEpoch_total_energy (η := ξLaw) hq hτ hγ hm hv M
  refine ⟨he.1,he.2.trans ?_⟩
  have hA (w : Ξ × (Fin M → Bool)) := sum_epoch_square M
    (fun r => ‖idealEpochDrift q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy r w‖^2)
  have hB (w : Ξ × (Fin M → Bool)) := sum_epoch_square M
    (fun r => ‖idealEpochInnovation q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy r w‖^2)
  simp_rw [hA,hB]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hb.1.2 (Nat.cast_nonneg q)) hb.2.2)
    (by positivity)

end
end SecondOrder
