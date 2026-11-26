import GradientHessian.CensoredControllerOracle
import GradientHessian.CensorPlanMeasurability

/-! Total reply functions for the chronological driver. Empty frontiers
receive a fixed zero reply. On every nonempty actual serve receipt these
functions equal the true physical jets, with one matrix product for an
ordinary reply. The zero branch is a totalization, not a claim about the
true objective after every leaf has retired. -/

noncomputable section
namespace GradientHessian.CensoredPolicy
universe u
open HigherHierarchy HierarchyParameters CensoredOracle ControllerCensor
open FrontierState TaskState TaskSlots ComparisonController GeometricDisclosure GeometricRepair JetLocality
open scoped InnerProductSpace

variable {Y E : Type u} {H : ℕ → Type u} {m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

def ordinaryReply (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (Z : Space Y E H m t) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) :=
  match hc : TaskState.current before with
  | none => 0
  | some leaf =>
    let p := planAt before after leaf hc t
    CensoredOracle.ordinaryDecoder K t p ((θ,Z),selectedMatrix t p (decode t θ) (numericalMap t Z))

def richReply (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (Z : Space Y E H m t) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) × (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ) :=
  match hc : TaskState.current before with
  | none => 0
  | some leaf => CensoredOracle.richDecoder K t (planAt before after leaf hc t) (θ,Z)

theorem ordinaryReply_current (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (leaf : Leaf (t+1))
    (hc : TaskState.current before=some leaf) (Z : Space Y E H m t) :
    ordinaryReply K t θ before after Z=CensoredOracle.ordinaryDecoder K t (planAt before after leaf hc t)
      ((θ,Z),selectedMatrix t (planAt before after leaf hc t) (decode t θ) (numericalMap t Z)) := by
  unfold ordinaryReply
  split
  · rename_i hn
    simp [hc] at hn
  · rename_i other he
    have h : other=leaf := Option.some.inj (he.symm.trans hc)
    subst other
    rfl

theorem richReply_current (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (leaf : Leaf (t+1))
    (hc : TaskState.current before=some leaf) (Z : Space Y E H m t) :
    richReply K t θ before after Z=CensoredOracle.richDecoder K t (planAt before after leaf hc t) (θ,Z) := by
  unfold richReply
  split
  · rename_i hn
    simp [hc] at hn
  · rename_i other he
    have h : other=leaf := Option.some.inj (he.symm.trans hc)
    subst other
    rfl

theorem ordinaryReply_none (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (hc : TaskState.current before=none) (Z : Space Y E H m t) :
    ordinaryReply K t θ before after Z=0 := by
  unfold ordinaryReply
  split
  · rfl
  · rename_i other he
    simp [hc] at he

theorem richReply_none (K : ℝ) (t : ℕ) (θ : Parameters Y E H m t)
    (before after : State (t+1) (m+1) ell) (hc : TaskState.current before=none) (Z : Space Y E H m t) :
    richReply K t θ before after Z=0 := by
  unfold richReply
  split
  · rfl
  · rename_i other he
    simp [hc] at he

theorem ordinaryReply_continuous {K : ℝ} (hK : 0<K) (t : ℕ)
    (before after : State (t+1) (m+1) ell) :
    Continuous (fun q : Parameters Y E H m t × Space Y E H m t => ordinaryReply K t q.1 before after q.2) := by
  cases hc : TaskState.current before with
  | none => simpa only [ordinaryReply_none K t _ before after hc] using (continuous_const : Continuous (fun _ :
      Parameters Y E H m t × Space Y E H m t => (0 : ℝ × (Space Y E H m t →L[ℝ] ℝ))))
  | some leaf =>
    simp only [ordinaryReply_current K t _ before after leaf hc]
    apply (CensoredOracle.ordinaryDecoder_continuous hK t (planAt before after leaf hc t)).comp
    exact continuous_id.prodMk (((selectedMatrix_contDiff t (planAt before after leaf hc t)).continuous.comp
      continuous_fst).clm_apply ((numericalMap (Y := Y) (E := E) (H := H) (m := m) t).continuous.comp continuous_snd))

theorem richReply_continuous {K : ℝ} (hK : 0<K) (t : ℕ)
    (before after : State (t+1) (m+1) ell) :
    Continuous (fun q : Parameters Y E H m t × Space Y E H m t => richReply K t q.1 before after q.2) := by
  cases hc : TaskState.current before with
  | none => simpa only [richReply_none K t _ before after hc] using (continuous_const : Continuous (fun _ :
      Parameters Y E H m t × Space Y E H m t => (0 : ℝ × (Space Y E H m t →L[ℝ] ℝ) ×
        (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ))))
  | some leaf =>
    simpa only [richReply_current K t _ before after leaf hc] using CensoredOracle.richDecoder_continuous (Y := Y) (E := E) (H := H)
      hK t (planAt before after leaf hc t)

theorem ordinaryReply_joint_measurable {K : ℝ} (hK : 0<K) (t : ℕ) :
    @Measurable ((Parameters Y E H m t × Space Y E H m t) ×
      (State (t+1) (m+1) ell × State (t+1) (m+1) ell))
      (ℝ × (Space Y E H m t →L[ℝ] ℝ))
      ((borel (Parameters Y E H m t × Space Y E H m t)).prod inferInstance) (borel _)
      (fun q => ordinaryReply K t q.1.1 q.2.1 q.2.2 q.1.2) := by
  letI : MeasurableSpace (Parameters Y E H m t × Space Y E H m t) := borel _
  letI : MeasurableSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ)) := borel _
  letI : BorelSpace (Parameters Y E H m t × Space Y E H m t) := ⟨rfl⟩
  letI : BorelSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ)) := ⟨rfl⟩
  exact measurable_from_prod_countable fun s => (ordinaryReply_continuous hK t s.1 s.2).measurable

theorem richReply_joint_measurable {K : ℝ} (hK : 0<K) (t : ℕ) :
    @Measurable ((Parameters Y E H m t × Space Y E H m t) ×
      (State (t+1) (m+1) ell × State (t+1) (m+1) ell))
      (ℝ × (Space Y E H m t →L[ℝ] ℝ) × (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ))
      ((borel (Parameters Y E H m t × Space Y E H m t)).prod inferInstance) (borel _)
      (fun q => richReply K t q.1.1 q.2.1 q.2.2 q.1.2) := by
  letI : MeasurableSpace (Parameters Y E H m t × Space Y E H m t) := borel _
  letI : MeasurableSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ) ×
    (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ)) := borel _
  letI : BorelSpace (Parameters Y E H m t × Space Y E H m t) := ⟨rfl⟩
  letI : BorelSpace (ℝ × (Space Y E H m t →L[ℝ] ℝ) ×
    (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ)) := ⟨rfl⟩
  exact measurable_from_prod_countable fun s => (richReply_continuous hK t s.1 s.2).measurable

theorem serve_richReply {K : ℝ} (hK : 0<K) (t : ℕ) (θ : Parameters Y E H m t)
    (s : State (t+1) (m+1) ell) (q : Pending (Space Y E H m t)) (hs : Ready s)
    (hclosed : LastChildClosed (TaskState.retired s)) (leaf : Leaf (t+1))
    (hc : TaskState.current (serve (rules K (decode t θ)) q s).beforeNormal=some leaf) :
    richJet (HigherHierarchy.scalar K t (decode t θ)) q.point=
      richReply K t θ (serve (rules K (decode t θ)) q s).beforeNormal
        (serve (rules K (decode t θ)) q s).afterNormal q.point := by
  rw [richReply_current K t θ _ _ leaf hc]
  exact serve_rich_decoder hK t θ s q hs hclosed leaf hc

variable [CompleteSpace Y]

theorem serve_ordinaryReply {K : ℝ} (hK : 0<K) (t : ℕ) (θ : Parameters Y E H m t)
    (s : State (t+1) (m+1) ell) (q : Pending (Space Y E H m t)) (hs : Ready s)
    (hclosed : LastChildClosed (TaskState.retired s)) (leaf : Leaf (t+1))
    (hc : TaskState.current (serve (rules K (decode t θ)) q s).beforeNormal=some leaf)
    (hsym : ∀ x z,⟪(leafCoefficients (decode t θ) leaf).A x,z⟫_ℝ=
      ⟪x,(leafCoefficients (decode t θ) leaf).A z⟫_ℝ) :
    ordinaryJet (HigherHierarchy.scalar K t (decode t θ)) q.point=
      ordinaryReply K t θ (serve (rules K (decode t θ)) q s).beforeNormal
        (serve (rules K (decode t θ)) q s).afterNormal q.point := by
  rw [ordinaryReply_current K t θ _ _ leaf hc,selectedMatrix_plan,numericalMap_eq]
  exact serve_ordinary_decoder hK t θ s q hs hclosed leaf hc hsym

end GradientHessian.CensoredPolicy
