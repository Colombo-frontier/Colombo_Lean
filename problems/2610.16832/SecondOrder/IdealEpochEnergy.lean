import SecondOrder.IdealEpochIncrements
import SecondOrder.ReindexEnergy

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

def idealEpochDrift {Ξ : Type*} {d M : ℕ} (q : ℕ) (L s : ℝ) (policy : Ξ → IdealPolicy d)
    (r : ℕ × ℕ) (w : Ξ × (Fin M → Bool)) : Point d :=
  ∑ i : Fin M, if idealEpochAddress q L s (policy w.1) i.val (signPrefix i w.2) = r then
    mixedIdealDrift L s policy i w else 0

theorem idealEpochDrift_eq {Ξ : Type*} {d M q : ℕ} (hq : 0 < q) (L s : ℝ)
    (policy : Ξ → IdealPolicy d) (r : ℕ × ℕ) (w : Ξ × (Fin M → Bool)) :
    idealEpochDrift q L s policy r w = ∑ i : Fin M,
      if epochAddress q (idealGradientFlag L s (policy w.1) (extendSigns w.2)) i.val = r then
        mixedIdealDrift L s policy i w else 0 := by
  simp only [idealEpochDrift,idealEpochAddress_prefix hq]

theorem epochAddress_mem_square (M q : ℕ) (g : ℕ → Bool) (i : Fin M) :
    epochAddress q g i.val ∈ (Finset.range M).product (Finset.range M) := by
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_range.mpr ((epochOfStep_le q g i.val).trans_lt i.isLt),
    Finset.mem_range.mpr ((Nat.sub_le i.val _).trans_lt i.isLt)⟩

/-- Reindexing onto actual epoch/local-time addresses preserves the entire
gradient energy pathwise, including stopped and empty executions. -/
theorem idealEpochDrift_total_energy {Ξ : Type*} {d M q : ℕ} (hq : 0 < q) (L s : ℝ)
    (policy : Ξ → IdealPolicy d) (w : Ξ × (Fin M → Bool)) :
    (∑ r ∈ (Finset.range M).product (Finset.range M), ‖idealEpochDrift q L s policy r w‖^2) =
      (idealRun L s (policy w.1) M w.2).gradientEnergy := by
  simp_rw [idealEpochDrift_eq hq]
  have hh := sum_injective_fiber_energy
    (fun i : Fin M => epochAddress q (idealGradientFlag L s (policy w.1) (extendSigns w.2)) i.val)
    ((epochAddress_injective hq _).comp Fin.val_injective) (fun i => mixedIdealDrift L s policy i w)
    _ (epochAddress_mem_square M q _)
  convert hh.trans (mixedIdealDrift_energy L s policy w) using 1 <;> congr 2
  funext r
  apply congrArg (fun z : Point d => ‖z‖^2)
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> rfl

theorem idealEpochInnovation_total_energy {Ξ : Type*} {d M q : ℕ} (hq : 0 < q) (L s : ℝ)
    (policy : Ξ → IdealPolicy d) (w : Ξ × (Fin M → Bool)) :
    (∑ r ∈ (Finset.range M).product (Finset.range M), ‖idealEpochInnovation q L s policy r w‖^2) =
      (idealRun L s (policy w.1) M w.2).curvatureEnergy := by
  simp_rw [idealEpochInnovation_eq hq]
  have hh := sum_injective_fiber_energy
    (fun i : Fin M => epochAddress q (idealGradientFlag L s (policy w.1) (extendSigns w.2)) i.val)
    ((epochAddress_injective hq _).comp Fin.val_injective) (fun i => mixedIdealInnovation L s policy i w)
    _ (epochAddress_mem_square M q _)
  convert hh.trans (mixedIdealInnovation_energy L s policy w) using 1 <;> congr 2
  funext r
  apply congrArg (fun z : Point d => ‖z‖^2)
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> rfl

theorem idealEpochDrift_support {Ξ : Type*} {d M q : ℕ} (hq : 0 < q) (L s : ℝ)
    (policy : Ξ → IdealPolicy d) (w : Ξ × (Fin M → Bool)) (e : ℕ) :
    (Finset.univ.filter (fun k : Fin M => idealEpochDrift q L s policy (e,k.val) w ≠ 0)).card ≤ q := by
  let g := idealGradientFlag L s (policy w.1) (extendSigns w.2)
  let S := Finset.univ.filter (fun k : Fin M => idealEpochDrift q L s policy (e,k.val) w ≠ 0)
  let T := (epochSteps M q g e).filter (fun i => mixedIdealDrift L s policy i w ≠ 0)
  have hs : S.image Fin.val ⊆ T.image (fun i => (epochAddress q g i.val).2) := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have hn := (Finset.mem_filter.mp hj).2
    rw [idealEpochDrift_eq hq] at hn
    obtain ⟨i,hi,hni⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    change (if epochAddress q g i.val = (e,j.val) then mixedIdealDrift L s policy i w else 0) ≠ 0 at hni
    have he : epochAddress q g i.val = (e,j.val) := by
      by_contra hne
      exact hni (if_neg hne)
    have hxi : mixedIdealDrift L s policy i w ≠ 0 := by
      simpa only [if_pos he] using hni
    apply Finset.mem_image.mpr
    exact ⟨i,Finset.mem_filter.mpr ⟨mem_epochSteps.mpr (congrArg Prod.fst he),hxi⟩,
      congrArg Prod.snd he⟩
  have hc := (Finset.card_le_card hs).trans (Finset.card_image_le (s := T))
  rw [Finset.card_image_of_injective S Fin.val_injective] at hc
  refine hc.trans ?_
  dsimp only [T]
  simp_rw [mixedIdealDrift_eq_path]
  exact pathDrift_epoch_support hq L s (policy w.1) (extendSigns w.2) e

theorem sum_epoch_square {V : Type*} [AddCommMonoid V] (M : ℕ) (f : ℕ × ℕ → V) :
    (∑ e : Fin M, ∑ k : Fin M, f (e.val,k.val)) =
      ∑ r ∈ (Finset.range M).product (Finset.range M), f r := by
  have hh (e : Fin M) : (∑ k : Fin M, f (e.val,k.val)) = ∑ k ∈ Finset.range M, f (e.val,k) :=
    Fin.sum_univ_eq_sum_range (fun k => f (e.val,k)) M
  simp_rw [hh]
  rw [Fin.sum_univ_eq_sum_range (fun e => ∑ k ∈ Finset.range M, f (e,k))]
  exact (Finset.sum_product _ _ _).symm

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.idealEpochDrift_moments (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M : ℕ) (r : ℕ × ℕ) :
    Integrable (idealEpochDrift (M := M) q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy r)
      (η.prod (signLaw M)) ∧
    Integrable (fun w => ‖idealEpochDrift q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy r w‖^2)
      (η.prod (signLaw M)) := by
  let a := mixedIdealDrift (M := M) P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy
  let label := fun (w : Ξ × (Fin M → Bool)) (i : Fin M) =>
    idealEpochAddress q P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) i.val (signPrefix i w.2)
  have hl (i : Fin M) : MeasurableSet {w | label w i = r} :=
    idealEpochAddress_selection_measurable hq _ _ hm r i
  have hi (i : Fin M) : Integrable (fun w => if label w i=r then a i w else 0) (η.prod (signLaw M)) := by
    convert (h.idealIncrement_integrable (η := η) hτ hγ hm hv i).1.indicator (hl i) using 1
    funext w
    simp [Set.indicator,a]
  have hi2 (i : Fin M) : Integrable (fun w => ‖if label w i=r then a i w else 0‖^2) (η.prod (signLaw M)) := by
    convert (h.idealIncrement_second_moments (η := η) hτ hγ hm hv i).1.indicator (hl i) using 1
    funext w
    simp only [Set.indicator,Set.mem_setOf_eq]
    split_ifs <;> simp [a]
  exact ⟨integrable_finset_sum _ (fun i _ => hi i),
    integrable_norm_sum_sq _ _ (fun i _ => hi i) (fun i _ => hi2 i)⟩

/-- Global bounds for the sum of the reindexed epoch energies, with no
factor proportional to the number of epochs. -/
theorem CommonLoss.idealEpoch_total_energy (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M : ℕ) :
    let a := idealEpochDrift (M := M) q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy
    let m := idealEpochInnovation (M := M) q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy
    let slots := (Finset.range M).product (Finset.range M)
    (Integrable (fun w => ∑ r ∈ slots, ‖a r w‖^2) (η.prod (signLaw M)) ∧
      (∫ w, ∑ r ∈ slots, ‖a r w‖^2 ∂η.prod (signLaw M)) ≤ P.gap/P.gradientLip) ∧
    (Integrable (fun w => ∑ r ∈ slots, ‖m r w‖^2) (η.prod (signLaw M)) ∧
      (∫ w, ∑ r ∈ slots, ‖m r w‖^2 ∂η.prod (signLaw M)) ≤ 16*P.gap/(3*γ)) := by
  dsimp only
  simp_rw [idealEpochDrift_total_energy hq,idealEpochInnovation_total_energy hq]
  exact h.measurableIdealRun_energy hτ hγ hm hv M

end
end SecondOrder
