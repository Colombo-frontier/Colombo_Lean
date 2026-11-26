import GradientHessian.CensoredJointCalculus
import GradientHessian.CensoredOracleView

/-! Continuous exact full-hierarchy decoders. The ordinary input view has
its selected matrix erased; the only supplied matrix-dependent quantity
is the one returned vector Ay. Physical derivatives are literal partial
derivatives of the C3 joint scalar and its explicit decomposition. -/

noncomputable section
namespace GradientHessian.CensoredOracle
universe u
open HigherHierarchy CensoredHierarchy HierarchyParameters PartialJetCalculus JetLocality
open scoped InnerProductSpace

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

def ordinaryRaw (K : ℝ) (t : ℕ) (p : Plan m t)
    (q : (Parameters Y E H m t × Space Y E H m t) × Y) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) :=
  let baseValue := Leaf.valueFromProduct (m+1 : ℕ) (Leaf.capRadius (m+1)) (numericalMap t q.1.2) q.2
  let baseFirst : Space Y E H m t →L[ℝ] ℝ := (innerSL ℝ (Leaf.gradientFromProduct (m+1 : ℕ) (Leaf.capRadius (m+1))
    (numericalMap t q.1.2) q.2)).comp (numericalMap t)
  (knownJoint K t p q.1+weightJoint K t p q.1*baseValue,
   partialFDeriv (knownJoint K t p) q.1 + weightJoint K t p q.1 • baseFirst +
    baseValue • partialFDeriv (weightJoint K t p) q.1)

def ordinaryDecoder (K : ℝ) (t : ℕ) (p : Plan m t)
    (q : (Parameters Y E H m t × Space Y E H m t) × Y) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) := ordinaryRaw K t p ((view false t p q.1.1,q.1.2),q.2)

def richRaw (K : ℝ) (t : ℕ) (p : Plan m t) (q : Parameters Y E H m t × Space Y E H m t) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) × (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ) :=
  (objectiveJoint K t p q,partialFDeriv (objectiveJoint K t p) q,
    partialFDeriv (partialFDeriv (objectiveJoint K t p)) q)

def richDecoder (K : ℝ) (t : ℕ) (p : Plan m t) (q : Parameters Y E H m t × Space Y E H m t) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) × (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ) :=
  richRaw K t p (view true t p q.1,q.2)

theorem decomposition_partials {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t)
    (θ : Parameters Y E H m t) (Z : Space Y E H m t) :
    partialFDeriv (knownJoint K t p) (θ,Z)=fderiv ℝ (known K t p (decode t θ)) Z ∧
    partialFDeriv (weightJoint K t p) (θ,Z)=fderiv ℝ (weight K t p (decode t θ)) Z :=
  ⟨partialFDeriv_eq θ Z ((joint_contDiff hK t p).1.differentiable (by decide) _),
   partialFDeriv_eq θ Z ((joint_contDiff hK t p).2.differentiable (by decide) _)⟩

theorem ordinaryRaw_continuous {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t) :
    Continuous (ordinaryRaw (Y := Y) (E := E) (H := H) K t p) := by
  have hk := (joint_contDiff (Y := Y) (E := E) (H := H) hK t p).1
  have hw := (joint_contDiff (Y := Y) (E := E) (H := H) hK t p).2
  have hk1 := (partialFDeriv_contDiff hk (by decide : (2:WithTop ℕ∞)+1≤3)).continuous
  have hw1 := (partialFDeriv_contDiff hw (by decide : (2:WithTop ℕ∞)+1≤3)).continuous
  let F := (Parameters Y E H m t × Space Y E H m t) × Y
  have hy : Continuous (fun q : F => (numericalMap t q.1.2,q.2)) :=
    ((numericalMap (Y := Y) (E := E) (H := H) (m := m) t).continuous.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd
  have hb := (Leaf.valueFromProduct_continuous (m+1 : ℕ) (Leaf.capRadius_pos (m := m+1) (by omega))).comp hy
  have hg := (Leaf.gradientFromProduct_continuous (m+1 : ℕ) (Leaf.capRadius_pos (m := m+1) (by omega))).comp hy
  have hd := ((innerSL ℝ : Y →L[ℝ] Y →L[ℝ] ℝ).continuous.comp hg).clm_comp
    (continuous_const : Continuous (fun _ : F => numericalMap (Y := Y) (E := E) (H := H) (m := m) t))
  exact ((hk.continuous.comp continuous_fst).add ((hw.continuous.comp continuous_fst).mul hb)).prodMk
    (((hk1.comp continuous_fst).add ((hw.continuous.comp continuous_fst).smul hd)).add
      (hb.smul (hw1.comp continuous_fst)))

theorem ordinaryDecoder_continuous {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t) :
    Continuous (ordinaryDecoder (Y := Y) (E := E) (H := H) K t p) :=
  (ordinaryRaw_continuous hK t p).comp
    ((((view_continuous false t p).comp (continuous_fst.comp continuous_fst)).prodMk
      (continuous_snd.comp continuous_fst)).prodMk continuous_snd)

theorem richRaw_continuous {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t) :
    Continuous (richRaw (Y := Y) (E := E) (H := H) K t p) := by
  have h := objectiveJoint_contDiff (Y := Y) (E := E) (H := H) hK t p
  have h1 := partialFDeriv_contDiff h (by decide : (2:WithTop ℕ∞)+1≤3)
  have h2 := partialFDeriv_contDiff h1 (by decide : (1:WithTop ℕ∞)+1≤2)
  exact h.continuous.prodMk (h1.continuous.prodMk h2.continuous)

theorem richDecoder_continuous {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t) :
    Continuous (richDecoder (Y := Y) (E := E) (H := H) K t p) :=
  (richRaw_continuous hK t p).comp (((view_continuous true t p).comp continuous_fst).prodMk continuous_snd)

theorem ordinaryRaw_erasure {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t)
    (θ η : Parameters Y E H m t) (he : SameKnown t p θ η) (Z : Space Y E H m t) (Ay : Y) :
    ordinaryRaw K t p ((θ,Z),Ay)=ordinaryRaw K t p ((η,Z),Ay) := by
  have hk := known_eq_of_sameKnown K t p θ η he
  have hw := weight_eq_of_sameKnown K t p θ η he
  simp only [ordinaryRaw,(decomposition_partials hK t p θ Z).1,(decomposition_partials hK t p θ Z).2,
    (decomposition_partials hK t p η Z).1,(decomposition_partials hK t p η Z).2,knownJoint,weightJoint,hk,hw]

theorem ordinaryDecoder_eq_raw {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t)
    (θ : Parameters Y E H m t) (Z : Space Y E H m t) (Ay : Y) :
    ordinaryDecoder K t p ((θ,Z),Ay)=ordinaryRaw K t p ((θ,Z),Ay) :=
  (ordinaryRaw_erasure hK t p θ _ (sameKnown_view false t p θ) Z Ay).symm

theorem scalar_eq_of_sameKnown (K : ℝ) (t : ℕ) (p : Plan m t)
    (θ η : Parameters Y E H m t) (he : SameKnown t p θ η)
    (hA : selectedMatrix t p (decode t θ)=selectedMatrix t p (decode t η)) :
    CensoredHierarchy.scalar K t p (decode t θ)=CensoredHierarchy.scalar K t p (decode t η) := by
  funext Z
  rw [scalar_decomposition,scalar_decomposition,known_eq_of_sameKnown K t p θ η he,
    weight_eq_of_sameKnown K t p θ η he,hA]

theorem richRaw_exact {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t)
    (θ : Parameters Y E H m t) (Z : Space Y E H m t) :
    richJet (CensoredHierarchy.scalar K t p (decode t θ)) Z=richRaw K t p (θ,Z) := by
  have h := objectiveJoint_contDiff (Y := Y) (E := E) (H := H) hK t p
  exact Prod.ext rfl (Prod.ext
    (partialFDeriv_eq θ Z (h.differentiable (by decide) _)).symm
    (partialFDeriv_twice_eq h θ Z).symm)

theorem richDecoder_exact {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t)
    (θ : Parameters Y E H m t) (Z : Space Y E H m t) :
    richJet (CensoredHierarchy.scalar K t p (decode t θ)) Z=richDecoder K t p (θ,Z) := by
  have he := scalar_eq_of_sameKnown K t p θ _ (sameKnown_view true t p θ)
    (by simpa only [if_true] using (selectedMatrix_view true t p θ).symm)
  rw [he]
  exact richRaw_exact hK t p _ Z

theorem ordinaryDecoder_erasure {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t)
    (θ η : Parameters Y E H m t) (he : SameKnown t p θ η) (Z : Space Y E H m t) (Ay : Y) :
    ordinaryDecoder K t p ((θ,Z),Ay)=ordinaryDecoder K t p ((η,Z),Ay) := by
  rw [ordinaryDecoder_eq_raw hK,ordinaryDecoder_eq_raw hK]
  exact ordinaryRaw_erasure hK t p θ η he Z Ay

theorem richDecoder_erasure {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t)
    (θ η : Parameters Y E H m t) (he : SameKnown t p θ η)
    (hA : selectedMatrix t p (decode t θ)=selectedMatrix t p (decode t η)) (Z : Space Y E H m t) :
    richDecoder K t p (θ,Z)=richDecoder K t p (η,Z) := by
  rw [← richDecoder_exact hK,← richDecoder_exact hK,scalar_eq_of_sameKnown K t p θ η he hA]

theorem ordinaryDecoder_borel {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t) :
    @Measurable ((Parameters Y E H m t × Space Y E H m t) × Y)
      (ℝ × (Space Y E H m t →L[ℝ] ℝ)) (borel _) (borel _) (ordinaryDecoder K t p) :=
  (ordinaryDecoder_continuous hK t p).borel_measurable

theorem richDecoder_borel {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t) :
    @Measurable (Parameters Y E H m t × Space Y E H m t)
      (ℝ × (Space Y E H m t →L[ℝ] ℝ) × (Space Y E H m t →L[ℝ] Space Y E H m t →L[ℝ] ℝ))
      (borel _) (borel _) (richDecoder K t p) := (richDecoder_continuous hK t p).borel_measurable

variable [CompleteSpace Y]

theorem ordinaryDecoder_exact {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t)
    (θ : Parameters Y E H m t) (hsym : ∀ x z,⟪selectedMatrix t p (decode t θ) x,z⟫_ℝ=
      ⟪x,selectedMatrix t p (decode t θ) z⟫_ℝ) (Z : Space Y E H m t) :
    ordinaryJet (CensoredHierarchy.scalar K t p (decode t θ)) Z=
      ordinaryDecoder K t p ((θ,Z),selectedMatrix t p (decode t θ) (numericalMap t Z)) := by
  rw [ordinaryDecoder_eq_raw hK]
  have hk : ContDiff ℝ 3 (known K t p (decode t θ)) := by
    have he : known K t p (decode t θ)=knownJoint K t p ∘ (fun x => (θ,x)) := rfl
    rw [he]; exact (joint_contDiff hK t p).1.comp (contDiff_const.prodMk contDiff_id)
  have hw : ContDiff ℝ 3 (weight K t p (decode t θ)) := by
    have he : weight K t p (decode t θ)=weightJoint K t p ∘ (fun x => (θ,x)) := rfl
    rw [he]; exact (joint_contDiff hK t p).2.comp (contDiff_const.prodMk contDiff_id)
  have hn := (LeafNumerical.base_hasGradientAt (M := (m+1:ℕ)) (Leaf.capRadius_pos (m := m+1) (by omega))
    (selectedMatrix t p (decode t θ)) hsym (numericalMap t Z)).hasFDerivAt
  have hb : HasFDerivAt (LeafNumerical.base (m+1:ℕ) (Leaf.capRadius (m+1)) (selectedMatrix t p (decode t θ)))
      (innerSL ℝ (Leaf.gradientFromProduct (m+1 : ℕ) (Leaf.capRadius (m+1))
        (numericalMap t Z) (selectedMatrix t p (decode t θ) (numericalMap t Z)))) (numericalMap t Z) := by
    convert hn using 1
  have hd := (hk.differentiable (by decide) Z).hasFDerivAt.add
    ((hw.differentiable (by decide) Z).hasFDerivAt.mul (hb.comp Z (numericalMap t).hasFDerivAt))
  have he : CensoredHierarchy.scalar K t p (decode t θ)=fun x => known K t p (decode t θ) x+
      weight K t p (decode t θ) x*LeafNumerical.base (m+1:ℕ) (Leaf.capRadius (m+1))
        (selectedMatrix t p (decode t θ)) (numericalMap t x) := funext (scalar_decomposition K t p (decode t θ))
  rw [he]
  apply Prod.ext
  · rfl
  · change fderiv ℝ _ Z = _
    simpa only [ordinaryRaw,(decomposition_partials hK t p θ Z).1,(decomposition_partials hK t p θ Z).2,
      knownJoint,weightJoint,Function.comp_apply,add_assoc] using hd.fderiv

end GradientHessian.CensoredOracle
