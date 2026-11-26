import SampleReuse.CurvatureFirstHessianCost
import SampleReuse.CurvatureFirstStoppedActive
import SampleReuse.CurvatureFirstStoppedQueryCounts
import SampleReuse.AncestorCostSum
import SampleReuse.PrefixCostSum

open SecondOrder
open scoped BigOperators Classical
namespace SampleReuse
noncomputable section

variable {Ω : Type*} {d T Bg BH M : ℕ}
  (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
  (f : Point d → ℝ) (F : Ω → Point d → ℝ)
  (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (x₀ : Point d) (w : Fin M → Bool)

theorem stoppedAcceptedSteps_le :
    stoppedAcceptedSteps hBg hBH P ε γ scaleG scaleH f F tape x₀ w ≤ M := by
  unfold stoppedAcceptedSteps
  calc
    _ ≤ ∑ _i : Fin M, 1 := Finset.sum_le_sum (fun i _ => by
      cases (stoppedTrajectoryAction hBg hBH P ε γ scaleG scaleH f F tape x₀ i w) <;>
        simp only [actionStepCount,Nat.zero_le,le_refl])
    _ = M := by simp

theorem curvatureStoppedRun_active_le_acceptedSteps {t : ℕ} (ht : t ≤ M)
    (ha : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).1 = true) :
    t ≤ stoppedAcceptedSteps hBg hBH P ε γ scaleG scaleH f F tape x₀ w := by
  let a (j : ℕ) := actionStepCount (stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape j
    (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ j))
  have hone (j : ℕ) (hj : j < t) : a j = 1 := by
    have hs := curvatureStoppedRun_active_before hBg hBH P ε γ scaleG scaleH f F tape
      (extendFiniteSigns w) x₀ (Nat.succ_le_of_lt hj) ha
    dsimp only [a]
    rw [curvatureStoppedStep_actionStepCount hBg hBH P ε γ scaleG scaleH f F tape j _ (extendFiniteSigns w j)]
    change (if (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ (j+1)).1 then 1 else 0) = 1
    simp only [hs,if_true]
  calc
    t = ∑ j ∈ Finset.range t, a j := by simp only [Finset.sum_congr rfl (fun j hj => hone j (Finset.mem_range.mp hj)),Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
    _ ≤ ∑ j ∈ Finset.range M, a j := Finset.sum_le_sum_of_subset (Finset.range_mono ht)
    _ = stoppedAcceptedSteps hBg hBH P ε γ scaleG scaleH f F tape x₀ w := by
      simp only [stoppedAcceptedSteps,stoppedTrajectoryAction,Finset.sum_range,a]

theorem curvatureStoppedRun_hessian_location_entry {j t : ℕ} (hjt : j < t)
    (ha : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).1 = true) :
    ((curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).2.2.2.2 j).1 =
      stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀ w j := by
  have hj := curvatureStoppedRun_active_before hBg hBH P ε γ scaleG scaleH f F tape
    (extendFiniteSigns w) x₀ hjt.le ha
  have hentry := curvatureMacroRun_hessianCache_entry hBg hBH P ε γ scaleG scaleH F tape
    (extendFiniteSigns w) x₀ hjt
  rw [← curvatureStoppedRun_eq_macro_of_active hBg hBH P ε γ scaleG scaleH f F tape
    (extendFiniteSigns w) x₀ t ha,
    ← curvatureStoppedRun_eq_macro_of_active hBg hBH P ε γ scaleG scaleH f F tape
    (extendFiniteSigns w) x₀ j hj] at hentry
  exact congrArg Prod.fst hentry

theorem curvatureFirstInspect_hessianCalls (t : ℕ) (s : OptimizerCache d) :
    (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).hessianCalls =
      checkpointCalls (B := BH) scaleH P.hessianNoise P.hessianLip t s.2.2.2 s.1 := by
  simp only [curvatureFirstInspect]
  split_ifs <;> rfl

theorem stoppedInspectionQueryCounts_hessian_of_active {t : ℕ}
    (ha : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).1 = true) :
    (stoppedInspectionQueryCounts hBg hBH P ε γ scaleG scaleH F tape t
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t)).2 =
      if t=0 then BH else 2*chordBatchSize scaleH P.hessianNoise P.hessianLip
        (stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀ w t)
        (stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀ w (ancestorParent t)) := by
  simp only [stoppedInspectionQueryCounts,ha,if_true,curvatureFirstInspect_hessianCalls]
  by_cases ht : t=0
  · simp only [checkpointCalls,if_pos ht]
  · simp only [checkpointCalls,checkpointBatchSize,if_neg ht]
    rw [curvatureStoppedRun_hessian_location_entry hBg hBH P ε γ scaleG scaleH f F tape x₀ w
      (ancestorParent_lt (Nat.pos_of_ne_zero ht)) ha]
    rfl

/-- Every actual shadow Hessian evaluation is charged to one chronological
ancestor edge, including the inspection that stops the process. -/
theorem curvatureStoppedQueryCounts_hessian_le_tree (depth : ℕ) (hd : M < 2^depth)
    (hcap : BH = batchSize scaleH (P.hessianNoise^2)) :
    (curvatureStoppedQueryCounts hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w)
      M 0 (true,optimizerInitial x₀)).2 ≤
        stoppedHessianCost hBg hBH P ε γ scaleG scaleH f F tape x₀ depth w := by
  let x := stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F tape x₀ w
  let n := stoppedAcceptedSteps hBg hBH P ε γ scaleG scaleH f F tape x₀ w
  let cost (t : ℕ) := (stoppedInspectionQueryCounts hBg hBH P ε γ scaleG scaleH F tape t
    (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t)).2
  let chord (t : ℕ) := chordBatchSize scaleH P.hessianNoise P.hessianLip (x t) (x (ancestorParent t))
  have hp (t : ℕ) (ht : t < M) : cost t ≤ if t ≤ n then (if t=0 then BH else 2*chord t) else 0 := by
    by_cases ha : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).1 = true
    · have hn := curvatureStoppedRun_active_le_acceptedSteps hBg hBH P ε γ scaleG scaleH f F tape x₀ w ht.le ha
      change t ≤ n at hn
      rw [if_pos hn]
      exact le_of_eq (stoppedInspectionQueryCounts_hessian_of_active hBg hBH P ε γ scaleG scaleH f F tape x₀ w ha)
    · have hc : cost t = 0 := by simp only [cost,stoppedInspectionQueryCounts,if_neg ha]
      rw [hc]
      exact Nat.zero_le _
  have hb := nat_sum_prefix_domination M n cost (fun t => if t=0 then BH else 2*chord t) hp
  rw [root_and_chord_sum] at hb
  have hn := stoppedAcceptedSteps_le hBg hBH P ε γ scaleG scaleH f F tape x₀ w
  change n ≤ M at hn
  have he : stoppedHessianCost hBg hBH P ε γ scaleG scaleH f F tape x₀ depth w =
      BH+2*∑ k ∈ Finset.Icc 1 n, chord k := by
    unfold stoppedHessianCost treeQueryCost
    dsimp only
    have heq := selected_ancestor_sum depth M n hn (hn.trans_lt hd)
      (fun r l => batchSize scaleH (min (P.hessianNoise^2) (P.hessianLip^2*‖x r-x l‖^2)))
    rw [← hcap]
    apply congrArg (fun q : ℕ => BH+2*q)
    simpa only [Finset.sum_filter,chord,chordBatchSize,x] using heq
  rw [he]
  change (curvatureStoppedQueryCounts hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w)
    M 0 (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ 0)).2 ≤ _
  rw [curvatureStoppedQueryCounts_eq_sum]
  simpa only [Prod.snd_sum,Nat.zero_add,cost] using hb

end
end SampleReuse
