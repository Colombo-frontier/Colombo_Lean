import GradientHessian.CensoredJointOracle
import GradientHessian.ControllerCensorGeometry

/-! The literal chronological controller's full physical reply factors
through the disclosed coefficient view and one selected matrix product. -/

noncomputable section
namespace GradientHessian.CensoredOracle
universe u
open HigherHierarchy CensoredHierarchy HierarchyParameters ControllerCensor
open FrontierState TaskState TaskSlots ComparisonController GeometricDisclosure GeometricRepair JetLocality
open scoped InnerProductSpace

variable {Y E : Type u} {H : ℕ → Type u} {m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

theorem numericalMap_eq (t : ℕ) : numericalMap (Y := Y) (E := E) (H := H) (m := m) t=
    HierarchyAddresses.numericalProjection t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [numericalMap,ih,HierarchyAddresses.numericalProjection_succ]

omit [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)] in
theorem selectedMatrix_plan (t : ℕ) (before after : State (t+1) (m+1) ell)
    (leaf : FrontierState.Leaf (t+1)) (hc : TaskState.current before=some leaf) (d : Data Y E H m t) :
    selectedMatrix t (planAt before after leaf hc t) d=(leafCoefficients d leaf).A := by
  rw [selectedMatrix,selectedLeaf_plan]
  rfl

theorem serve_rich_decoder {K : ℝ} (hK : 0<K) (t : ℕ) (θ : Parameters Y E H m t)
    (s : State (t+1) (m+1) ell) (q : Pending (Space Y E H m t)) (hs : Ready s)
    (hclosed : LastChildClosed (TaskState.retired s)) (leaf : FrontierState.Leaf (t+1))
    (hc : TaskState.current (serve (rules K (decode t θ)) q s).beforeNormal=some leaf) :
    richJet (HigherHierarchy.scalar K t (decode t θ)) q.point=
      richDecoder K t (planAt (serve (rules K (decode t θ)) q s).beforeNormal
        (serve (rules K (decode t θ)) q s).afterNormal leaf hc t) (θ,q.point) :=
  (ControllerCensor.serve_richJet K (decode t θ) s q hs hclosed leaf hK hc).trans
    (richDecoder_exact hK t _ θ q.point)

variable [CompleteSpace Y]

theorem serve_ordinary_decoder {K : ℝ} (hK : 0<K) (t : ℕ) (θ : Parameters Y E H m t)
    (s : State (t+1) (m+1) ell) (q : Pending (Space Y E H m t)) (hs : Ready s)
    (hclosed : LastChildClosed (TaskState.retired s)) (leaf : FrontierState.Leaf (t+1))
    (hc : TaskState.current (serve (rules K (decode t θ)) q s).beforeNormal=some leaf)
    (hsym : ∀ x z,⟪(leafCoefficients (decode t θ) leaf).A x,z⟫_ℝ=
      ⟪x,(leafCoefficients (decode t θ) leaf).A z⟫_ℝ) :
    ordinaryJet (HigherHierarchy.scalar K t (decode t θ)) q.point=
      ordinaryDecoder K t (planAt (serve (rules K (decode t θ)) q s).beforeNormal
        (serve (rules K (decode t θ)) q s).afterNormal leaf hc t)
        ((θ,q.point),(leafCoefficients (decode t θ) leaf).A (HierarchyAddresses.numericalProjection t q.point)) := by
  have he := SecondJetAlgebra.ordinaryJet_eq_of_richJet_eq
    (ControllerCensor.serve_richJet K (decode t θ) s q hs hclosed leaf hK hc)
  apply he.trans
  have hsym' : ∀ x z,⟪selectedMatrix t (planAt (serve (rules K (decode t θ)) q s).beforeNormal
      (serve (rules K (decode t θ)) q s).afterNormal leaf hc t) (decode t θ) x,z⟫_ℝ=
      ⟪x,selectedMatrix t (planAt (serve (rules K (decode t θ)) q s).beforeNormal
      (serve (rules K (decode t θ)) q s).afterNormal leaf hc t) (decode t θ) z⟫_ℝ := by
    simpa only [selectedMatrix_plan] using hsym
  simpa only [selectedMatrix_plan,numericalMap_eq] using ordinaryDecoder_exact hK t
    (planAt (serve (rules K (decode t θ)) q s).beforeNormal
      (serve (rules K (decode t θ)) q s).afterNormal leaf hc t) θ hsym' q.point

end GradientHessian.CensoredOracle
