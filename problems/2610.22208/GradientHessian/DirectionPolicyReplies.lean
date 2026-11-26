import GradientHessian.CensoredCompletedReplies
import GradientHessian.HierarchyJointJets

/-! A measurable totalization for direction-censored policy replies. The
retirement guard is true on every actual receipt. Empty frontiers receive
the true completed jet, so the totalization is also globally correct there. -/

noncomputable section
namespace GradientHessian.DirectionPolicy
universe u
open Classical HigherHierarchy HierarchyParameters ControllerCensor FrontierState
  TaskState TaskSlots ComparisonController GeometricDisclosure GeometricRepair

variable {Y E : Type u} {H : ℕ → Type u} {m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

def ordinary (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (Z : Space Y E H m t) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) :=
  if TaskState.retired before⊆TaskState.retired after then CensoredPolicy.completedOrdinary K t θ before after Z else 0

def rich (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (Z : Space Y E H m t) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) × (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ) :=
  if TaskState.retired before⊆TaskState.retired after then CensoredPolicy.completedRich K t θ before after Z else 0

theorem receipt_monotone {L M ell : ℕ} {X A : Type*} (R : Rules L M ell X A)
    (p : Pending X) (s : State L M ell) (hs : Ready s) :
    TaskState.retired (serve R p s).beforeNormal⊆TaskState.retired (serve R p s).afterNormal :=
  ComparisonControllerInvariant.normal_retired_mono R p (repairRun_ready R p (8^L) hs)

theorem ordinary_receipt (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (R : Rules (t+1) (m+1) ell (Space Y E H m t) A) (p : Pending (Space Y E H m t))
    (s : State (t+1) (m+1) ell) (hs : Ready s) :
    ordinary K t θ (serve R p s).beforeNormal (serve R p s).afterNormal p.point=
      CensoredPolicy.completedOrdinary K t θ (serve R p s).beforeNormal (serve R p s).afterNormal p.point := by
  simp only [ordinary,if_pos (receipt_monotone R p s hs)]

theorem rich_receipt (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (R : Rules (t+1) (m+1) ell (Space Y E H m t) A) (p : Pending (Space Y E H m t))
    (s : State (t+1) (m+1) ell) (hs : Ready s) :
    rich K t θ (serve R p s).beforeNormal (serve R p s).afterNormal p.point=
      CensoredPolicy.completedRich K t θ (serve R p s).beforeNormal (serve R p s).afterNormal p.point := by
  simp only [rich,if_pos (receipt_monotone R p s hs)]

theorem active_of_hidden_node {L M ell : ℕ} (before after : State L M ell)
    (hm : TaskState.retired before⊆TaskState.retired after) (v : Node L)
    (hd : ¬NodeDisclosed after v) : TaskState.current before≠none := by
  intro hc
  have hall := (FrontierState.current_none_iff (TaskState.retired before)).mp hc
  apply hd
  intro leaf _
  apply hm
  rw [hall]
  exact Finset.mem_univ _

theorem active_of_hidden_task {L M ell : ℕ} (before after : State L M ell)
    (hm : TaskState.retired before⊆TaskState.retired after) (leaf : Leaf L) (j : Fin M)
    (hd : ¬TaskDisclosed after leaf j) : TaskState.current before≠none := by
  apply active_of_hidden_node before after hm (leafNode leaf)
  intro he
  exact hd (retired_all_tasks_disclosed ((leafNode_disclosed after leaf).mp he) j)

theorem replies_eq {K : ℝ} (hK : 0<K) (t : ℕ) (θ η : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell)
    (hactive : TaskState.retired before⊆TaskState.retired after → TaskState.current before≠none)
    (hknown : ∀ hm : TaskState.retired before⊆TaskState.retired after,
      ∀ cur (hc : TaskState.current before=some cur),CensoredOracle.SameKnown t (planAt before after cur hc t) θ η)
    (hA : ∀ p,CensoredOracle.selectedMatrix t p (decode t θ)=CensoredOracle.selectedMatrix t p (decode t η))
    (Z : Space Y E H m t) :
    ordinary K t θ before after Z=ordinary K t η before after Z ∧
      rich K t θ before after Z=rich K t η before after Z := by
  by_cases hm : TaskState.retired before⊆TaskState.retired after
  · simp only [ordinary,rich,if_pos hm,CensoredPolicy.completedOrdinary_active K t _ before after (hactive hm),
      CensoredPolicy.completedRich_active K t _ before after (hactive hm)]
    cases hc : TaskState.current before with
    | none => exact False.elim (hactive hm hc)
    | some cur =>
      rw [CensoredPolicy.ordinaryReply_current _ _ _ _ _ cur hc,
        CensoredPolicy.ordinaryReply_current _ _ _ _ _ cur hc,
        CensoredPolicy.richReply_current _ _ _ _ _ cur hc,CensoredPolicy.richReply_current _ _ _ _ _ cur hc,hA]
      exact ⟨CensoredOracle.ordinaryDecoder_erasure hK t _ θ η (hknown hm cur hc) Z _,
        CensoredOracle.richDecoder_erasure hK t _ θ η (hknown hm cur hc) (hA _) Z⟩
  · simp only [ordinary,rich,if_neg hm,and_self]

theorem ordinary_continuous {K : ℝ} (hK : 0<K) (t : ℕ)
    (before after : State (t+1) (m+1) ell) :
    Continuous (fun q : Parameters Y E H m t × Space Y E H m t => ordinary K t q.1 before after q.2) := by
  unfold ordinary CensoredPolicy.completedOrdinary
  split_ifs
  · simpa only [ordinaryJet_decode hK] using (HierarchyParameters.ordinaryDecoder_continuous (Y := Y) (E := E) (H := H) (m := m) hK t)
  · exact CensoredPolicy.ordinaryReply_continuous hK t before after
  · exact continuous_const

theorem rich_continuous {K : ℝ} (hK : 0<K) (t : ℕ)
    (before after : State (t+1) (m+1) ell) :
    Continuous (fun q : Parameters Y E H m t × Space Y E H m t => rich K t q.1 before after q.2) := by
  unfold rich CensoredPolicy.completedRich
  split_ifs
  · simpa only [richJet_decode hK] using (HierarchyParameters.richDecoder_continuous (Y := Y) (E := E) (H := H) (m := m) hK t)
  · exact CensoredPolicy.richReply_continuous hK t before after
  · exact continuous_const

theorem ordinary_joint_measurable {K : ℝ} (hK : 0<K) (t : ℕ) :
    @Measurable ((Parameters Y E H m t × Space Y E H m t) ×
      (State (t+1) (m+1) ell × State (t+1) (m+1) ell))
      (ℝ × (Space Y E H m t →L[ℝ] ℝ))
      ((borel (Parameters Y E H m t × Space Y E H m t)).prod inferInstance) (borel _)
      (fun q => ordinary K t q.1.1 q.2.1 q.2.2 q.1.2) := by
  letI : MeasurableSpace (Parameters Y E H m t × Space Y E H m t) := borel _
  letI : MeasurableSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ)) := borel _
  letI : BorelSpace (Parameters Y E H m t × Space Y E H m t) := ⟨rfl⟩
  letI : BorelSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ)) := ⟨rfl⟩
  exact measurable_from_prod_countable fun s => (ordinary_continuous hK t s.1 s.2).measurable

theorem rich_joint_measurable {K : ℝ} (hK : 0<K) (t : ℕ) :
    @Measurable ((Parameters Y E H m t × Space Y E H m t) ×
      (State (t+1) (m+1) ell × State (t+1) (m+1) ell))
      (ℝ × (Space Y E H m t →L[ℝ] ℝ) × (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ))
      ((borel (Parameters Y E H m t × Space Y E H m t)).prod inferInstance) (borel _)
      (fun q => rich K t q.1.1 q.2.1 q.2.2 q.1.2) := by
  letI : MeasurableSpace (Parameters Y E H m t × Space Y E H m t) := borel _
  letI : MeasurableSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ) ×
    (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ)) := borel _
  letI : BorelSpace (Parameters Y E H m t × Space Y E H m t) := ⟨rfl⟩
  letI : BorelSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ) ×
    (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ)) := ⟨rfl⟩
  exact measurable_from_prod_countable fun s => (rich_continuous hK t s.1 s.2).measurable

end GradientHessian.DirectionPolicy
