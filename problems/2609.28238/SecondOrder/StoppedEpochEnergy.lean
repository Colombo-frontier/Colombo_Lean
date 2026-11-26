import SecondOrder.StoppedEpochPath

open MeasureTheory
open scoped BigOperators Classical InnerProductSpace

namespace SecondOrder
noncomputable section

variable {Ω E : Type*} {m₀ : MeasurableSpace Ω} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The general stopped-epoch extension in `up:lem:dyadicenergy`.
Both endpoints of each epoch are stopping times, the intervals partition
the capped physical timeline, and unused epochs may have zero length.
The path consists of the original physical points, frozen at each end.
No independence or sign-symmetry assumption is imposed on the L2
martingale differences. The universal energy constant is two. -/
theorem stopped_epoch_chord_energy (M N L q : ℕ)
    (start finish : Fin N → Ω → ℕ) (hpart : StoppedEpochPartition M N start finish)
    (hcap : ∀ e w, finish e w≤M)
    (past : ℕ → MeasurableSpace Ω) (hp : ∀ t, past t≤m₀) (hmono : Monotone past)
    (hstart : ∀ e t, MeasurableSet[past t] {w | start e w≤t})
    (hfinish : ∀ e t, MeasurableSet[past t] {w | finish e w≤t})
    (x : Ω → ℕ → E) (a m : Fin M → Ω → E)
    (hx : ∀ w i, x w (i.val+1)-x w i.val=a i w+m i w)
    (ha : ∀ i, MemLp (a i) 2 μ) (hm : ∀ i, MemLp (m i) 2 μ)
    (hadapt : ∀ i j, i<j → AEStronglyMeasurable[past j.val] (m i) μ)
    (hzero : ∀ j, μ[m j | past j.val]=ᵐ[μ] (fun _ => 0))
    (hs : ∀ e w, (Finset.univ.filter (fun k : Fin M =>
      reindexedMartingale a (stoppedEpochAddress start finish hpart) (e,k) w≠0)).card≤q) :
    Integrable (fun w => ∑ e, ∑ i ∈ completedNodes L (finish e w-start e w),
      ‖stoppedEpochPath start finish x e w (nodeRight i)-
        stoppedEpochPath start finish x e w (nodeLeft i)‖^2) μ ∧
    (∫ w, ∑ e, ∑ i ∈ completedNodes L (finish e w-start e w),
      ‖stoppedEpochPath start finish x e w (nodeRight i)-
        stoppedEpochPath start finish x e w (nodeLeft i)‖^2 ∂μ)≤
      2*(L:ℝ)*((q:ℝ)*(∫ w, ∑ i, ‖a i w‖^2 ∂μ)+(∫ w, ∑ i, ‖m i w‖^2 ∂μ)) := by
  have hlen (e : Fin N) : Measurable (fun w => finish e w-start e w) :=
    (stoppingTime_measurable past hp (finish e) (hfinish e)).sub
      (stoppingTime_measurable past hp (start e) (hstart e))
  exact predictable_epoch_chord_energy M N M L q a m (stoppedEpochAddress start finish hpart)
    (fun i => past i.val) (fun i => hp i.val) (fun i j hij => hmono hij)
    ha hm hadapt hzero (stoppedEpochAddress_predictable start finish hpart past hmono hstart hfinish)
    (stoppedEpochAddress_injective start finish hpart) (fun e w => finish e w-start e w) hlen
    (fun e w => (Nat.sub_le _ _).trans (hcap e w)) (stoppedEpochPath start finish x)
    (stoppedEpochPath_displacement start finish hpart x a m hx hcap) hs

end
end SecondOrder
