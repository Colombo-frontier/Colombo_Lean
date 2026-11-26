import NCConcave16991.MixedHaarNativeCoordinates
import NCConcave16991.MixedHaarFrameStepLaw
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-! # Native mixed vertex requests and the actual sparse oracle reply -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000

attribute [local irreducible] nativeCoordinates nativeVertexOperator Haar.orthogonalLinearIsometryEquiv

theorem measurable_from_sigma_native {J : Type*} {A : J → Type*} {B : Type*}
    [∀ j, MeasurableSpace (A j)] [MeasurableSpace B] (f : (Σ j, A j) → B)
    (hf : ∀ j, Measurable (fun a : A j ↦ f ⟨j,a⟩)) : Measurable f := by
  intro t ht
  change MeasurableSet[⨅ j, (inferInstance : MeasurableSpace (A j)).map (Sigma.mk j)] (f ⁻¹' t)
  rw [MeasurableSpace.measurableSet_iInf]
  intro j
  change MeasurableSet ((fun a : A j ↦ f ⟨j,a⟩) ⁻¹' t)
  exact hf j ht

variable {I : Type*} [Fintype I] (E : I → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]

abbrev NativeRequest := Σ i, E i ⊕ E i
abbrev NativeReply := ∀ i, E i

def nativeRequestAt (i : I) (q : NativeRequest E) : E i ⊕ E i := by
  classical
  exact if h : q.1 = i then h ▸ q.2 else .inl 0

theorem nativeRequestAt_measurable (i : I) : Measurable (nativeRequestAt E i) := by
  classical
  apply measurable_from_sigma_native
  intro j
  by_cases h : j = i
  · subst j
    have he : (fun a : E i ⊕ E i ↦ nativeRequestAt E i ⟨i,a⟩) =
        (id : E i ⊕ E i → E i ⊕ E i) := by
      funext a
      simp [nativeRequestAt]
    rw [he]
    exact measurable_id
  · simpa only [nativeRequestAt,dif_neg h] using
      (measurable_const : Measurable (fun _ : E j ⊕ E j ↦ (Sum.inl 0 : E i ⊕ E i)))

theorem nativeRequest_index_measurableSet (i : I) :
    MeasurableSet {q : NativeRequest E | q.1 = i} := by
  have hm : Measurable (fun q : NativeRequest E ↦ q.1 = i) := by
    apply measurable_from_sigma_native
    intro j
    change Measurable (fun _ : E j ⊕ E j ↦ j = i)
    exact measurable_const
  exact hm.setOf

def nativeCoordinateRequest (i : I) (q : NativeRequest E) : FrameRequest (nativeDimension E i) :=
  Sum.map (nativeCoordinates E i) (nativeCoordinates E i) (nativeRequestAt E i q)

theorem nativeCoordinateRequest_measurable (i : I) : Measurable (nativeCoordinateRequest E i) :=
  ((nativeCoordinates E i).continuous.measurable.sumMap (nativeCoordinates E i).continuous.measurable).comp
    (nativeRequestAt_measurable E i)

def coordinateReply {k : ℕ} (Q : Haar.OrthogonalGroup k) (q : FrameRequest k) : Space k :=
  q.elim (Haar.orthogonalLinearIsometryEquiv Q) (Haar.orthogonalLinearIsometryEquiv Q⁻¹)

theorem coordinateReply_measurable {k : ℕ} :
    Measurable (fun p : Haar.OrthogonalGroup k × FrameRequest k ↦ coordinateReply p.1 p.2) := by
  have hf : Measurable (fun p : Haar.OrthogonalGroup k × Space k ↦ Haar.orthogonalLinearIsometryEquiv p.1 p.2) :=
    sphereAction_joint_measurable
  have hg : Measurable (fun p : Haar.OrthogonalGroup k × Space k ↦ Haar.orthogonalLinearIsometryEquiv p.1⁻¹ p.2) :=
    sphereAction_joint_measurable.comp (measurable_fst.inv.prodMk measurable_snd)
  have h := (hf.sumElim hg).comp
    (MeasurableEquiv.prodSumDistrib (Haar.OrthogonalGroup k) (Space k) (Space k)).measurable
  convert h using 1
  funext p
  rcases p with ⟨Q,a | b⟩ <;> rfl

theorem frameStaticStep_reply {k : ℕ} (s : FrameState k) (q : FrameRequest k) (Q : Haar.OrthogonalGroup k) :
    (frameStaticStep s q Q).2 = coordinateReply Q q := by
  cases q <;> rfl

def nativeRequestAnswer (Q : NativeOrthogonal E) (q : NativeRequest E) : NativeReply E := by
  classical
  exact fun i ↦ if q.1 = i then
    (nativeCoordinates E i).symm (coordinateReply (Q i) (nativeCoordinateRequest E i q)) else 0

theorem nativeRequestAnswer_measurable :
    Measurable (fun p : NativeOrthogonal E × NativeRequest E ↦ nativeRequestAnswer E p.1 p.2) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  have hQ := (measurable_pi_apply i).comp (measurable_fst : Measurable (Prod.fst : NativeOrthogonal E × NativeRequest E → NativeOrthogonal E))
  have hq : Measurable (fun p : NativeOrthogonal E × NativeRequest E ↦ nativeCoordinateRequest E i p.2) :=
    (nativeCoordinateRequest_measurable E i).comp measurable_snd
  have hr := (nativeCoordinates E i).symm.continuous.measurable.comp
    (coordinateReply_measurable.comp (hQ.prodMk hq))
  exact Measurable.ite ((nativeRequest_index_measurableSet E i).preimage measurable_snd) hr measurable_const

theorem nativeRequestAnswer_forward (Q : NativeOrthogonal E) (i : I) (a : E i) :
    nativeRequestAnswer E Q ⟨i,.inl a⟩ i = nativeVertexOperator E Q i a := by
  simp [nativeRequestAnswer,nativeCoordinateRequest,nativeRequestAt,coordinateReply,nativeVertexOperator_apply]

theorem nativeRequestAnswer_inverse (Q : NativeOrthogonal E) (i : I) (b : E i) :
    nativeRequestAnswer E Q ⟨i,.inr b⟩ i = (nativeVertexOperator E Q i).symm b := by
  simp [nativeRequestAnswer,nativeCoordinateRequest,nativeRequestAt,coordinateReply,nativeVertexOperator_symm_apply]

theorem nativeRequestAnswer_unselected (Q : NativeOrthogonal E) (q : NativeRequest E) (i : I) (hi : q.1 ≠ i) :
    nativeRequestAnswer E Q q i = 0 := by
  simp only [nativeRequestAnswer,if_neg hi]

end NCConcave16991.MixedHaar
