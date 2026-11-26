import FreshGradientMinimax.AcceleratedLabels
import FreshGradientMinimax.Transcript

/-! The unstopped accelerated auxiliary run depends only on the labels
already exposed. The terminal output enjoys the same independence. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
namespace Algorithm
variable {n k D : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm D D Seed)

def acceleratedLabelQuery (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (L ε : ℝ) (t : ℕ) (seed : Seed) : Joint D D :=
  A.query t (A.deterministicRun (acceleratedLabelReply z L ε) t seed)

def acceleratedLabelOutput (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (L ε : ℝ) (H : ℕ) (seed : Seed) : Euclid D :=
  A.output H (A.deterministicRun (acceleratedLabelReply z L ε) H seed)

theorem acceleratedLabelRun_congr (L ε : ℝ) (seed : Seed) (t : ℕ)
    {z z' : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D}
    (h : ∀ i, acceleratedLabelStage n k i ≤ t → z i = z' i) :
    A.deterministicRun (acceleratedLabelReply z L ε) t seed =
      A.deterministicRun (acceleratedLabelReply z' L ε) t seed := by
  refine A.first_exit_transcript_identity _ _ seed t ?_ t le_rfl
  intro s hs
  apply congrFun (acceleratedLabelReply_congr L ε ?_)
  intro i hi
  exact h i (by omega)

theorem acceleratedLabelQuery_update_hidden (L ε : ℝ) (seed : Seed) (t : ℕ)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (i : Fin ((k * 2 + 1) + k * (n + 2))) (hi : t < acceleratedLabelStage n k i) (j : Fin D) :
    A.acceleratedLabelQuery (Function.update z i j) L ε t seed = A.acceleratedLabelQuery z L ε t seed := by
  unfold acceleratedLabelQuery
  rw [A.acceleratedLabelRun_congr L ε seed t]
  intro a ha
  have hai : a ≠ i := by intro he; subst a; omega
  exact Function.update_of_ne hai j z

theorem acceleratedLabelOutput_update_hidden (L ε : ℝ) (seed : Seed) (H : ℕ)
    (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (i : Fin ((k * 2 + 1) + k * (n + 2))) (hi : H < acceleratedLabelStage n k i) (j : Fin D) :
    A.acceleratedLabelOutput (Function.update z i j) L ε H seed = A.acceleratedLabelOutput z L ε H seed := by
  unfold acceleratedLabelOutput
  rw [A.acceleratedLabelRun_congr L ε seed H]
  intro a ha
  have hai : a ≠ i := by intro he; subst a; omega
  exact Function.update_of_ne hai j z

theorem acceleratedLabelQuery_measurable (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (hk : 0 < k) (L ε : ℝ) (t : ℕ) : Measurable (A.acceleratedLabelQuery z L ε t) :=
  (A.query_measurable t).comp
    (A.deterministicRun_measurable _ (acceleratedLabelReply_measurable z hk L ε) t)

theorem acceleratedLabelOutput_measurable (z : Fin ((k * 2 + 1) + k * (n + 2)) → Fin D)
    (hk : 0 < k) (L ε : ℝ) (H : ℕ) : Measurable (A.acceleratedLabelOutput z L ε H) :=
  (A.output_measurable H).comp
    (A.deterministicRun_measurable _ (acceleratedLabelReply_measurable z hk L ε) H)

end Algorithm
end FreshGradientMinimax
