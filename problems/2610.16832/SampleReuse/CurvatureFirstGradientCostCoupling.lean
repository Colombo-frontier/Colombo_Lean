import SampleReuse.CurvatureFirstGradientCost
import SampleReuse.CurvatureFirstStoppedGradientLocations
import SampleReuse.AncestorCostSum

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

variable {Ω : Type*} {d T Bg BH M : ℕ}
  (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
  (f : Point d → ℝ) (F : Ω → Point d → ℝ)
  (g : SampleTape ((T+1)*Bg) Ω) (hh : SampleTape ((T+1)*BH) Ω)
  (x₀ : Point d) (w : Fin M → Bool)

def stoppedGradientCharge (k : ℕ) : ℕ :=
  if k=0 then Bg else 2*chordBatchSize scaleG P.gradientNoise P.gradientLip
    (stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ w
      (stoppedGradientTime hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ k w))
    (stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ w
      (stoppedGradientTime hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ (ancestorParent k) w))

theorem curvatureFirstInspect_gradientCalls (t : ℕ) (s : OptimizerCache d) :
    (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F (derivativeTapes g hh) t s).gradientCalls =
      if curvatureTag (sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F (derivativeTapes g hh) t s))
      then 0 else checkpointCalls (B := Bg) scaleG P.gradientNoise P.gradientLip s.2.1 s.2.2.1 s.1 := by
  simp only [curvatureFirstInspect,inspectionHessian]
  split_ifs <;> rfl

theorem stoppedInspectionQueryCounts_gradient_charge {t : ℕ} (htM : t≤M) (htT : t≤T)
    (ha : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t).1=true)
    (htag : ¬curvatureTag (sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F (derivativeTapes g hh) t
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t).2))=true) :
    (stoppedInspectionQueryCounts hBg hBH P ε γ scaleG scaleH F (derivativeTapes g hh) t
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t)).1 =
      stoppedGradientCharge hBg hBH P ε γ scaleG scaleH f F g hh x₀ w
        (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t).2.2.1 := by
  have hτ := stoppedGradientTime_eq_of_active_tag hBg hBH P ε γ scaleG scaleH f F
    (derivativeTapes g hh) x₀ w t htM ha htag
  simp only [stoppedInspectionQueryCounts,ha,if_true,curvatureFirstInspect_gradientCalls,if_neg htag,
    stoppedGradientCharge,checkpointCalls,checkpointBatchSize]
  split_ifs with hk
  · rfl
  · rw [stoppedGradientCache_location_before hBg hBH P ε γ scaleG scaleH f F g hh x₀ w _ t htM htT ha
      (ancestorParent_lt (Nat.pos_of_ne_zero hk)),hτ]
    rfl

theorem stopped_gradient_queries_le_charges (hMT : M≤T+1) :
    (∑ t ∈ Finset.range M, (stoppedInspectionQueryCounts hBg hBH P ε γ scaleG scaleH F (derivativeTapes g hh) t
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t)).1) ≤
      ∑ k ∈ Finset.Icc 0
        (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ M).2.2.1,
        stoppedGradientCharge hBg hBH P ε γ scaleG scaleH f F g hh x₀ w k := by
  let s t := curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t
  let tag t := curvatureTag (sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F (derivativeTapes g hh) t (s t).2))
  let q := (Finset.range M).filter (fun t => (s t).1=true ∧ ¬tag t=true)
  let charge := stoppedGradientCharge hBg hBH P ε γ scaleG scaleH f F g hh x₀ w
  have hcount (t : ℕ) (ht : t∈Finset.range M) :
      (stoppedInspectionQueryCounts hBg hBH P ε γ scaleG scaleH F (derivativeTapes g hh) t (s t)).1 =
        if (s t).1=true ∧ ¬tag t=true then charge (s t).2.2.1 else 0 := by
    by_cases ha : (s t).1=true
    · by_cases hb : tag t=true
      · simp only [stoppedInspectionQueryCounts,ha,if_true,curvatureFirstInspect_gradientCalls,
          show curvatureTag (sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F (derivativeTapes g hh) t (s t).2))=true from hb,
          hb,if_true,not_true_eq_false,and_false,if_false]
      · rw [if_pos ⟨ha,hb⟩]
        exact stoppedInspectionQueryCounts_gradient_charge hBg hBH P ε γ scaleG scaleH f F g hh x₀ w
          (Finset.mem_range.mp ht).le (by have := Finset.mem_range.mp ht; omega) ha hb
    · simp only [stoppedInspectionQueryCounts,if_neg ha,false_and,ha,if_false,Bool.false_eq_true]
  have hinj : Set.InjOn (fun t => (s t).2.2.1) (q : Set ℕ) := by
    intro t ht u hu he
    have ht' := Finset.mem_filter.mp ht
    have hu' := Finset.mem_filter.mp hu
    have hτt := stoppedGradientTime_eq_of_active_tag hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ w t
      (Finset.mem_range.mp ht'.1).le ht'.2.1 ht'.2.2
    have hτu := stoppedGradientTime_eq_of_active_tag hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ w u
      (Finset.mem_range.mp hu'.1).le hu'.2.1 hu'.2.2
    rw [show (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t).2.2.1 =
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ u).2.2.1 from he,hτu] at hτt
    exact hτt.symm
  have hsub : q.image (fun t => (s t).2.2.1) ⊆ Finset.Icc 0 (s M).2.2.1 := by
    intro k hk
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hk
    refine Finset.mem_Icc.mpr ⟨Nat.zero_le _,?_⟩
    exact curvatureStoppedRun_gradientClock_mono hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh)
      (extendFiniteSigns w) x₀ (Finset.mem_range.mp (Finset.mem_filter.mp ht).1).le
  calc
    _ = ∑ t ∈ q, charge (s t).2.2.1 := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl hcount
    _ = ∑ k ∈ q.image (fun t => (s t).2.2.1), charge k := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

theorem stopped_gradient_queries_le_cost (hMT : M≤T+1) (depth : ℕ) (hd : M<2^depth)
    (hcap : Bg=batchSize scaleG (P.gradientNoise^2)) :
    (∑ t ∈ Finset.range M, (stoppedInspectionQueryCounts hBg hBH P ε γ scaleG scaleH F (derivativeTapes g hh) t
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t)).1) ≤
      stoppedGradientCost hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ depth w := by
  apply (stopped_gradient_queries_le_charges hBg hBH P ε γ scaleG scaleH f F g hh x₀ w hMT).trans_eq
  let n := (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ M).2.2.1
  have hn : n≤M := curvatureStoppedRun_gradientClock_le_time hBg hBH P ε γ scaleG scaleH f F
    (derivativeTapes g hh) (extendFiniteSigns w) x₀ M
  have hset : Finset.Icc 0 n=insert 0 (Finset.Icc 1 n) := by ext k; simp; omega
  rw [show (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ M).2.2.1=n from rfl,hset,
    Finset.sum_insert (by simp)]
  simp only [stoppedGradientCharge,if_pos rfl,if_true]
  rw [stoppedGradientCost,treeQueryCost,selected_ancestor_sum depth M n hn (hn.trans_lt hd)
    (fun k p => batchSize scaleG (min (P.gradientNoise^2) (P.gradientLip^2*
      ‖stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ w
        (stoppedGradientTime hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ k w) -
        stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ w
        (stoppedGradientTime hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ p w)‖^2)))]
  rw [← hcap,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k≠0 := by have := (Finset.mem_Icc.mp hk).1; omega
  simp only [if_neg hk0,chordBatchSize]

theorem actual_gradient_queries_le_cost (hMT : M≤T+1) (depth : ℕ) (hd : M<2^depth)
    (hcap : Bg=batchSize scaleG (P.gradientNoise^2))
    (hv : curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh)
      M 0 (optimizerInitial x₀) w) :
    (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F (derivativeTapes g hh)
      (extendFiniteSigns w) M 0 (optimizerInitial x₀)).1 ≤
      stoppedGradientCost hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ depth w := by
  have he := curvatureStoppedQueryCounts_eq_actual_of_valid hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh)
    (extendFiniteSigns w) M 0 (optimizerInitial x₀) w (by intro i; simp only [Nat.zero_add,extendFiniteSigns,dif_pos i.isLt]) hv
  rw [← he]
  change (curvatureStoppedQueryCounts hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh)
    (extendFiniteSigns w) M 0 (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F
      (derivativeTapes g hh) (extendFiniteSigns w) x₀ 0)).1 ≤ _
  rw [curvatureStoppedQueryCounts_eq_sum]
  simp only [Nat.zero_add,Prod.fst_sum]
  exact stopped_gradient_queries_le_cost hBg hBH P ε γ scaleG scaleH f F g hh x₀ w hMT depth hd hcap

end
end SampleReuse
