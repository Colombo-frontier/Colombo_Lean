import SampleReuse.CurvatureFirstTrajectory

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem checkpointPacket_congr_tape {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H d B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (reserve : ℕ → Fin B → Fin H) (k : ℕ) (cache : TreeCache d E) (x : Point d)
    (tape tape' : SampleTape H Ω) (heq : ∀ i, tape (reserve k i) = tape' (reserve k i)) :
    checkpointPacket hB scale σ L sample reserve k cache x tape =
      checkpointPacket hB scale σ L sample reserve k cache x tape' := by
  unfold checkpointPacket
  split_ifs
  · exact batchMeanTape_congr_tape _ _ tape tape' heq
  · exact batchMeanTape_congr_tape _ _ tape tape' (fun i => heq (prefixHandles hB _ i))

theorem curvatureFirstInspect_congr_tape {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape tape' : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (t : ℕ) (s : OptimizerCache d)
    (hh : ∀ i, tape (hessianReserve T Bg BH t i) = tape' (hessianReserve T Bg BH t i))
    (hg : ∀ i, tape (gradientReserve T Bg BH s.2.1 i) = tape' (gradientReserve T Bg BH s.2.1 i)) :
    curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s =
      curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape' t s := by
  have heH := checkpointPacket_congr_tape hBH scaleH P.hessianNoise P.hessianLip
    (fun z => hessian (F z)) (hessianReserve T Bg BH) t s.2.2.2 s.1 tape tape' hh
  have heG := checkpointPacket_congr_tape hBg scaleG P.gradientNoise P.gradientLip
    (fun z => gradient (F z)) (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1 tape tape' hg
  simp only [curvatureFirstInspect,heH,heG]

/-- The entire state before Hessian checkpoint t depends only on previous
Hessian blocks and the separate gradient tape. The private signs may be fixed
in full; no future Hessian sample is inspected by this execution. -/
theorem curvatureMacroRun_depends_hessian_past {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape tape' : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) (t : ℕ)
    (hh : ∀ j < t, ∀ i, tape (hessianReserve T Bg BH j i) = tape' (hessianReserve T Bg BH j i))
    (hg : ∀ j i, tape (gradientReserve T Bg BH j i) = tape' (gradientReserve T Bg BH j i)) :
    curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t =
      curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape' signs x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hs := ih (fun j hj => hh j (Nat.lt_succ_of_lt hj))
    simp only [curvatureMacroRun,hs]
    rw [curvatureFirstInspect_congr_tape hBg hBH P ε γ scaleG scaleH F tape tape' t _
      (hh t (Nat.lt_succ_self t)) (hg _)]

/-- An inspection that has not advanced the gradient clock past k never reads
gradient block k. On a curvature branch it reads no gradient samples at all. -/
theorem curvatureFirstInspect_congr_gradient_past {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape tape' : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t k : ℕ) (s : OptimizerCache d)
    (hh : ∀ i, tape (hessianReserve T Bg BH t i) = tape' (hessianReserve T Bg BH t i))
    (hg : ∀ j < k, ∀ i, tape (gradientReserve T Bg BH j i) = tape' (gradientReserve T Bg BH j i))
    (hnext : (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).cache.2.1 ≤ k) :
    curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s =
      curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape' t s := by
  have heH := checkpointPacket_congr_tape hBH scaleH P.hessianNoise P.hessianLip
    (fun z => hessian (F z)) (hessianReserve T Bg BH) t s.2.2.2 s.1 tape tape' hh
  simp only [curvatureFirstInspect,heH] at hnext ⊢
  by_cases ht : curvatureTag (sourceCurvatureSelector (3*γ/4)
      (inspectionHessian hBH P scaleH F tape' t s)) = true
  · simp only [inspectionHessian] at ht
    simp only [if_pos ht]
  · simp only [inspectionHessian] at ht
    simp only [if_neg ht] at hnext ⊢
    have hi : s.2.1 < k := Nat.lt_of_succ_le hnext
    have heG := checkpointPacket_congr_tape hBg scaleG P.gradientNoise P.gradientLip
      (fun z => gradient (F z)) (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1 tape tape' (hg _ hi)
    rw [heG]

/-- Before the kth gradient packet is installed, the actual state cannot
depend on that packet or any later gradient block. The Hessian tape can be
fixed in full, so this result supports the asynchronous gradient checkpoints. -/
theorem curvatureMacroRun_depends_gradient_past {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape tape' : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) (t k : ℕ)
    (hh : ∀ j i, tape (hessianReserve T Bg BH j i) = tape' (hessianReserve T Bg BH j i))
    (hg : ∀ j < k, ∀ i, tape (gradientReserve T Bg BH j i) = tape' (gradientReserve T Bg BH j i))
    (hindex : (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t).2.1 ≤ k) :
    curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t =
      curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape' signs x₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev := (curvatureMacroRun_gradientIndex_mono hBg hBH P ε γ scaleG scaleH F tape signs x₀
      (Nat.le_succ t)).trans hindex
    have hs := ih hprev
    have hn : (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t)).cache.2.1 ≤ k := hindex
    rw [hs] at hn
    simp only [curvatureMacroRun,hs]
    rw [curvatureFirstInspect_congr_gradient_past hBg hBH P ε γ scaleG scaleH F tape tape' t k _
      (hh t) hg hn]

/-- Whether the kth gradient checkpoint has occurred is itself independent
of gradient blocks k and later. This includes the event that it never occurs
within a specified deterministic outer horizon. -/
theorem curvatureMacroRun_gradient_clock_event {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape tape' : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) (t k : ℕ)
    (hh : ∀ j i, tape (hessianReserve T Bg BH j i) = tape' (hessianReserve T Bg BH j i))
    (hg : ∀ j < k, ∀ i, tape (gradientReserve T Bg BH j i) = tape' (gradientReserve T Bg BH j i)) :
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t).2.1 ≤ k ↔
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape' signs x₀ t).2.1 ≤ k := by
  constructor
  · intro ht
    rwa [curvatureMacroRun_depends_gradient_past hBg hBH P ε γ scaleG scaleH F tape tape' signs x₀ t k hh hg ht] at ht
  · intro ht
    rwa [curvatureMacroRun_depends_gradient_past hBg hBH P ε γ scaleG scaleH F tape' tape signs x₀ t k
      (fun j i => (hh j i).symm) (fun j hj i => (hg j hj i).symm) ht] at ht

end
end SampleReuse
