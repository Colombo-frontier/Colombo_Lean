import GradientHessian.CensoredLeafController
import GradientHessian.JetPullback

/-! Exact full ambient leaf replies after the geometric pass. The ordinary
decoder takes one numerical product and the disclosed coefficient view;
the rich decoder takes the disclosed matrix. All maps are jointly continuous
for each fixed finite controller state. -/

noncomputable section
namespace GradientHessian.CensoredLeaf.Physical
open JetLocality

variable {Y E F : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}

def ordinaryDecoder (L : F →L[ℝ] Leaf.Space Y E m) (mask : Mask m)
    (p : (Leaf.Marks Y E m × F) × Y) : ℝ × (F →L[ℝ] ℝ) :=
  JetPullback.ordinary 1 L (CensoredLeaf.ordinaryDecoder mask ((p.1.1,L p.1.2),p.2))

def richDecoder (L : F →L[ℝ] Leaf.Space Y E m) (mask : Mask m)
    (p : Leaf.MatrixMarks Y E m × F) : ℝ × (F →L[ℝ] ℝ) × (F →L[ℝ] F →L[ℝ] ℝ) :=
  JetPullback.rich 1 L (CensoredLeaf.richDecoder mask (p.1,L p.2))

theorem ordinaryDecoder_continuous (hm : 1≤m) (L : F →L[ℝ] Leaf.Space Y E m) (mask : Mask m) :
    Continuous (ordinaryDecoder L mask) := by
  have hp : Continuous (fun p : (Leaf.Marks Y E m × F) × Y => ((p.1.1,L p.1.2),p.2)) :=
    ((continuous_fst.comp continuous_fst).prodMk
      (L.continuous.comp (continuous_snd.comp continuous_fst))).prodMk continuous_snd
  exact (JetPullback.ordinary_continuous 1 L).comp
    ((CensoredLeaf.ordinaryDecoder_continuous hm mask).comp hp)

theorem richDecoder_continuous (hm : 1≤m) (L : F →L[ℝ] Leaf.Space Y E m) (mask : Mask m) :
    Continuous (richDecoder L mask) :=
  (JetPullback.rich_continuous 1 L).comp
    ((CensoredLeaf.richDecoder_continuous hm mask).comp
      (continuous_fst.prodMk (L.continuous.comp continuous_snd)))

theorem ordinaryDecoder_borel (hm : 1≤m) (L : F →L[ℝ] Leaf.Space Y E m) (mask : Mask m) :
    @Measurable ((Leaf.Marks Y E m × F) × Y) (ℝ × (F →L[ℝ] ℝ))
      (borel _) (borel _) (ordinaryDecoder L mask) :=
  (ordinaryDecoder_continuous hm L mask).borel_measurable

theorem richDecoder_borel (hm : 1≤m) (L : F →L[ℝ] Leaf.Space Y E m) (mask : Mask m) :
    @Measurable (Leaf.MatrixMarks Y E m × F) (ℝ × (F →L[ℝ] ℝ) × (F →L[ℝ] F →L[ℝ] ℝ))
      (borel _) (borel _) (richDecoder L mask) :=
  (richDecoder_continuous hm L mask).borel_measurable

theorem ordinaryDecoder_erasure (L : F →L[ℝ] Leaf.Space Y E m) (mask : Mask m)
    {θ η : Leaf.Marks Y E m} (he : view mask θ=view mask η) (x : F) (Ay : Y) :
    ordinaryDecoder L mask ((θ,x),Ay)=ordinaryDecoder L mask ((η,x),Ay) := by
  unfold ordinaryDecoder
  rw [CensoredLeaf.ordinaryDecoder_erasure mask he]

theorem richDecoder_erasure (hm : 1≤m) (L : F →L[ℝ] Leaf.Space Y E m) (mask : Mask m)
    (A : Y →L[ℝ] Y) {θ η : Leaf.Marks Y E m} (he : view mask θ=view mask η) (x : F) :
    richDecoder L mask ((A,θ),x)=richDecoder L mask ((A,η),x) := by
  unfold richDecoder
  rw [CensoredLeaf.richDecoder_erasure hm mask A he]

theorem richJet_known_matrix (hm : 1≤m) (L : F →L[ℝ] Leaf.Space Y E m) (mask : Mask m)
    (A : Y →L[ℝ] Y) (θ : Leaf.Marks Y E m) (x : F) :
    richJet (objective mask A θ ∘ L) x=richDecoder L mask ((A,θ),x) := by
  have he := JetPullback.rich_exact 1 L ((objective_contDiff hm mask A θ).of_le (by decide)) x
  have hf : JetPullback.scalar 1 L (objective mask A θ)=objective mask A θ ∘ L := by
    funext y
    simp only [JetPullback.scalar,one_mul,Function.comp_apply]
  rw [hf] at he
  rw [he,CensoredLeaf.richJet_known_matrix hm]
  rfl

variable [CompleteSpace Y]
open scoped InnerProductSpace

theorem ordinaryJet_one_product (hm : 1≤m) (L : F →L[ℝ] Leaf.Space Y E m) (mask : Mask m)
    (A : Y →L[ℝ] Y) (hsym : ∀ x z,⟪A x,z⟫_ℝ=⟪x,A z⟫_ℝ)
    (θ : Leaf.Marks Y E m) (x : F) :
    ordinaryJet (objective mask A θ ∘ L) x=ordinaryDecoder L mask
      ((θ,x),A (InnerCoordinates.numerical Y E m (Inner.absoluteDepth+2) (L x))) := by
  have he := JetPullback.ordinary_exact 1 L
    ((objective_contDiff hm mask A θ).differentiable (by decide)) x
  have hf : JetPullback.scalar 1 L (objective mask A θ)=objective mask A θ ∘ L := by
    funext y
    simp only [JetPullback.scalar,one_mul,Function.comp_apply]
  rw [hf] at he
  rw [he,CensoredLeaf.ordinaryJet_one_product hm mask A hsym]
  rfl

end GradientHessian.CensoredLeaf.Physical

namespace GradientHessian.CensoredLeaf
universe u
open Classical JetLocality FrontierState TaskState TaskSlots ComparisonController
open scoped InnerProductSpace

variable {Y E : Type u} {H : ℕ → Type u} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

theorem terminal_rich_decoder (K : ℝ) (data : HigherHierarchy.Data Y E H m t)
    (s : State (t+1) (m+1) ell) (p : Pending (HigherHierarchy.Space Y E H m t))
    (hs : Ready s) (ht : choose (GeometricRepair.rules K data) p s=none)
    (leaf : FrontierState.Leaf (t+1)) (hc : TaskState.current s=some leaf) :
    richJet ((Leaf.objective (GeometricRepair.leafCoefficients data leaf).A
      (GeometricRepair.leafCoefficients data leaf).b (GeometricRepair.leafCoefficients data leaf).a
      (GeometricRepair.leafCoefficients data leaf).v) ∘ HierarchyAddresses.leafProjection t) p.point=
    Physical.richDecoder (HierarchyAddresses.leafProjection t)
      (stateMask s (normal (GeometricRepair.rules K data) p s) leaf hc)
      (((GeometricRepair.leafCoefficients data leaf).A,leafMarks data leaf),p.point) :=
  (terminal_physical_leaf_richJet K data s p hs ht leaf hc).trans
    (Physical.richJet_known_matrix (by omega) _ _ _ _ _)

variable [CompleteSpace Y]

theorem terminal_ordinary_decoder (K : ℝ) (data : HigherHierarchy.Data Y E H m t)
    (s : State (t+1) (m+1) ell) (p : Pending (HigherHierarchy.Space Y E H m t))
    (hs : Ready s) (ht : choose (GeometricRepair.rules K data) p s=none)
    (leaf : FrontierState.Leaf (t+1)) (hc : TaskState.current s=some leaf)
    (hsym : ∀ x z,⟪(GeometricRepair.leafCoefficients data leaf).A x,z⟫_ℝ=
      ⟪x,(GeometricRepair.leafCoefficients data leaf).A z⟫_ℝ) :
    ordinaryJet ((Leaf.objective (GeometricRepair.leafCoefficients data leaf).A
      (GeometricRepair.leafCoefficients data leaf).b (GeometricRepair.leafCoefficients data leaf).a
      (GeometricRepair.leafCoefficients data leaf).v) ∘ HierarchyAddresses.leafProjection t) p.point=
    Physical.ordinaryDecoder (HierarchyAddresses.leafProjection t)
      (stateMask s (normal (GeometricRepair.rules K data) p s) leaf hc)
      ((leafMarks data leaf,p.point),(GeometricRepair.leafCoefficients data leaf).A
        (HierarchyAddresses.numericalProjection t p.point)) :=
  (SecondJetAlgebra.ordinaryJet_eq_of_richJet_eq
    (terminal_physical_leaf_richJet K data s p hs ht leaf hc)).trans
    (Physical.ordinaryJet_one_product (by omega) _ _ _ hsym _ _)

end GradientHessian.CensoredLeaf
