import SecondOrder.PredictableMartingaleReindex
import SecondOrder.EpochDyadicEnergy
import SecondOrder.TreeCostEnergy

open MeasureTheory
open scoped BigOperators Classical InnerProductSpace

namespace SecondOrder
noncomputable section

variable {Ω E : Type*} {m₀ : MeasurableSpace Ω} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- All random epochs together, represented by their predictable physical-
time addresses. The martingale part is any genuine L2 difference sequence.
The bound charges every physical increment once, without an epoch factor. -/
theorem predictable_epoch_chord_energy (M N K L q : ℕ)
    (a m : Fin M → Ω → E) (label : Fin M → Ω → Fin N × Fin K)
    (past : Fin M → MeasurableSpace Ω) (hp : ∀ j, past j≤m₀) (hmono : Monotone past)
    (ha : ∀ i, MemLp (a i) 2 μ) (hm : ∀ i, MemLp (m i) 2 μ)
    (hadapt : ∀ i j, i<j → AEStronglyMeasurable[past j] (m i) μ)
    (hzero : ∀ j, μ[m j | past j]=ᵐ[μ] (fun _ => 0))
    (hl : ∀ r i, MeasurableSet[past i] {w | label i w=r})
    (hinj : ∀ w, Function.Injective (fun i => label i w))
    (length : Fin N → Ω → ℕ) (hlen : ∀ e, Measurable (length e))
    (hcap : ∀ e w, length e w≤K) (x : Fin N → Ω → ℕ → E)
    (hx : ∀ e w k, x e w (k.val+1)-x e w k.val=
      reindexedMartingale a label (e,k) w+reindexedMartingale m label (e,k) w)
    (hs : ∀ e w, (Finset.univ.filter (fun k : Fin K =>
      reindexedMartingale a label (e,k) w≠0)).card≤q) :
    Integrable (fun w => ∑ e, ∑ i ∈ completedNodes L (length e w),
      ‖x e w (nodeRight i)-x e w (nodeLeft i)‖^2) μ ∧
    (∫ w, ∑ e, ∑ i ∈ completedNodes L (length e w),
      ‖x e w (nodeRight i)-x e w (nodeLeft i)‖^2 ∂μ)≤
      2*(L:ℝ)*((q:ℝ)*(∫ w, ∑ i, ‖a i w‖^2 ∂μ)+(∫ w, ∑ i, ‖m i w‖^2 ∂μ)) := by
  let A := fun e k => reindexedMartingale a label (e,k)
  let Z := fun e k => reindexedMartingale m label (e,k)
  have hA (e : Fin N) (k : Fin K) :=
    reindexedMartingale_moments a label (e,k) (fun i => hp i _ (hl (e,k) i)) ha
  have hZ (e : Fin N) (k : Fin K) :=
    reindexedMartingale_moments m label (e,k) (fun i => hp i _ (hl (e,k) i)) hm
  have ho (e : Fin N) (i j : Fin K) (hij : i≠j) :
      (∫ w, ⟪Z e i w,Z e j w⟫_ℝ ∂μ)=0 :=
    reindexedMartingale_orthogonal m label past hp hmono hm hadapt hzero hl (e,i) (e,j)
      (fun he => hij (congrArg Prod.snd he))
  have hb := integral_epoch_dyadic_energy N K L q A Z
    (fun e k => (hA e k).1) (fun e k => (hZ e k).1)
    (fun e k => (hA e k).2) (fun e k => (hZ e k).2) hs ho
  have hactual : Integrable (fun w => ∑ e, ∑ i ∈ completedNodes L (length e w),
      ‖x e w (nodeRight i)-x e w (nodeLeft i)‖^2) μ := by
    apply integrable_finset_sum
    intro e _
    exact completed_chord_energy_integrable K L (length e) (hlen e) (hcap e) (x e)
      (A e) (Z e) (hx e) (fun k => (hA e k).1) (fun k => (hZ e k).1)
      (fun k => (hA e k).2) (fun k => (hZ e k).2)
  have hle (w : Ω) : (∑ e, ∑ i ∈ completedNodes L (length e w),
      ‖x e w (nodeRight i)-x e w (nodeLeft i)‖^2)≤
      ∑ e, ∑ i : Fin L × Fin K, ‖∑ k ∈ dyadicBlock K i.1.val i.2, (A e k w+Z e k w)‖^2 := by
    apply Finset.sum_le_sum
    intro e _
    rw [sum_completedNodes_finite (hcap e w)]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : nodeRight (paddedNode i)≤length e w
    · rw [if_pos hi]
      have ht := dyadicBlock_telescopes (x e w) i (hi.trans (hcap e w))
      simp_rw [hx] at ht
      exact le_of_eq (congrArg (fun v => ‖v‖^2) ht.symm)
    · rw [if_neg hi]
      exact sq_nonneg _
  have heA (w : Ω) : (∑ e, ∑ k, ‖A e k w‖^2)=∑ i, ‖a i w‖^2 := by
    simpa only [Fintype.sum_prod_type,A] using
      reindexedMartingale_energy a label hinj Finset.univ (fun _ _ => Finset.mem_univ _) w
  have heZ (w : Ω) : (∑ e, ∑ k, ‖Z e k w‖^2)=∑ i, ‖m i w‖^2 := by
    simpa only [Fintype.sum_prod_type,Z] using
      reindexedMartingale_energy m label hinj Finset.univ (fun _ _ => Finset.mem_univ _) w
  refine ⟨hactual,(integral_mono hactual hb.1 hle).trans ?_⟩
  simpa only [heA,heZ] using hb.2

end
end SecondOrder
