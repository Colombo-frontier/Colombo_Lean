import GradientHessian.CensoredLeafScalar

/-! Full physical decoders for the explicit censored leaf. The ordinary
decoder's only matrix-dependent input is the one returned vector Ay.
Every derivative here is an actual Frechet derivative of the displayed
scalar. Equality with the original leaf is a separate flatness theorem. -/

noncomputable section
namespace GradientHessian.CensoredLeaf

open InnerCoordinates JetLocality PartialJetCalculus
open scoped InnerProductSpace

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

theorem knownTerm_partial_fderiv (mask : Mask m) (θ : Leaf.Marks Y E m) (Z : Leaf.Space Y E m) :
    fderiv ℝ (knownTerm mask θ) Z=partialFDeriv (knownJoint mask) (θ,Z) :=
  (partialFDeriv_eq θ Z ((knownJoint_contDiff (Y := Y) (E := E) mask).differentiable
    (by decide : (1:WithTop ℕ∞) ≤ 3) (θ,Z))).symm

theorem knownTerm_partial_continuous (mask : Mask m) :
    Continuous (fun p : Leaf.Marks Y E m × Leaf.Space Y E m => fderiv ℝ (knownTerm mask p.1) p.2) := by
  simp_rw [knownTerm_partial_fderiv]
  exact (partialFDeriv_contDiff (knownJoint_contDiff (Y := Y) (E := E) mask)
    (by decide : (2:WithTop ℕ∞)+1 ≤ 3)).continuous

def ordinaryDecoder (mask : Mask m) (p : (Leaf.Marks Y E m × Leaf.Space Y E m) × Y) :
    ℝ × (Leaf.Space Y E m →L[ℝ] ℝ) :=
  (Leaf.valueFromProduct m (Leaf.capRadius m) (numerical Y E m (Inner.absoluteDepth+2) p.1.2) p.2 +
      knownTerm mask p.1.1 p.1.2,
    (innerSL ℝ (Leaf.gradientFromProduct m (Leaf.capRadius m)
      (numerical Y E m (Inner.absoluteDepth+2) p.1.2) p.2)).comp (numerical Y E m (Inner.absoluteDepth+2)) +
      fderiv ℝ (knownTerm mask p.1.1) p.1.2)

theorem ordinaryDecoder_continuous (hm : 1≤m) (mask : Mask m) :
    Continuous (ordinaryDecoder (Y := Y) (E := E) mask) := by
  have hp : Continuous (fun p : (Leaf.Marks Y E m × Leaf.Space Y E m) × Y =>
      (numerical Y E m (Inner.absoluteDepth+2) p.1.2,p.2)) :=
    ((numerical Y E m (Inner.absoluteDepth+2)).continuous.comp
      (continuous_snd.comp continuous_fst)).prodMk continuous_snd
  have hval := ((Leaf.valueFromProduct_continuous (m:ℝ) (Leaf.capRadius_pos hm)).comp hp).add
    ((knownJoint_contDiff (Y := Y) (E := E) mask).continuous.comp continuous_fst)
  have hgrad := (Leaf.gradientFromProduct_continuous (m:ℝ) (Leaf.capRadius_pos hm)).comp hp
  have hcov := ((innerSL ℝ : Y →L[ℝ] Y →L[ℝ] ℝ).continuous.comp hgrad).clm_comp
    (continuous_const : Continuous (fun _ : (Leaf.Marks Y E m × Leaf.Space Y E m) × Y =>
      numerical Y E m (Inner.absoluteDepth+2)))
  exact hval.prodMk (hcov.add ((knownTerm_partial_continuous mask).comp continuous_fst))

theorem ordinaryDecoder_borel (hm : 1≤m) (mask : Mask m) :
    @Measurable ((Leaf.Marks Y E m × Leaf.Space Y E m) × Y) (ℝ × (Leaf.Space Y E m →L[ℝ] ℝ))
      (borel _) (borel _) (ordinaryDecoder mask) :=
  (ordinaryDecoder_continuous hm mask).borel_measurable

theorem ordinaryDecoder_erasure (mask : Mask m) {θ η : Leaf.Marks Y E m}
    (he : view mask θ=view mask η) (Z : Leaf.Space Y E m) (product : Y) :
    ordinaryDecoder mask ((θ,Z),product)=ordinaryDecoder mask ((η,Z),product) := by
  simp only [ordinaryDecoder,knownTerm_erasure mask he]

@[simp] theorem ordinaryDecoder_view (mask : Mask m) (θ : Leaf.Marks Y E m)
    (Z : Leaf.Space Y E m) (product : Y) :
    ordinaryDecoder mask ((view mask θ,Z),product)=ordinaryDecoder mask ((θ,Z),product) :=
  ordinaryDecoder_erasure mask (view_idempotent mask θ) Z product

def richDecoder (mask : Mask m) (p : Leaf.MatrixMarks Y E m × Leaf.Space Y E m) :
    ℝ × (Leaf.Space Y E m →L[ℝ] ℝ) × (Leaf.Space Y E m →L[ℝ] (Leaf.Space Y E m →L[ℝ] ℝ)) :=
  (objectiveJoint mask p,partialFDeriv (objectiveJoint mask) p,
    partialFDeriv (partialFDeriv (objectiveJoint mask)) p)

theorem richDecoder_continuous (hm : 1≤m) (mask : Mask m) :
    Continuous (richDecoder (Y := Y) (E := E) mask) := by
  have hc := objectiveJoint_contDiff (Y := Y) (E := E) hm mask
  have h1 := partialFDeriv_contDiff hc (by decide : (2:WithTop ℕ∞)+1 ≤ 3)
  have h2 := partialFDeriv_contDiff h1 (by decide : (1:WithTop ℕ∞)+1 ≤ 2)
  exact hc.continuous.prodMk (h1.continuous.prodMk h2.continuous)

theorem richDecoder_borel (hm : 1≤m) (mask : Mask m) :
    @Measurable (Leaf.MatrixMarks Y E m × Leaf.Space Y E m)
      (ℝ × (Leaf.Space Y E m →L[ℝ] ℝ) × (Leaf.Space Y E m →L[ℝ] (Leaf.Space Y E m →L[ℝ] ℝ)))
      (borel _) (borel _) (richDecoder mask) := (richDecoder_continuous hm mask).borel_measurable

theorem richJet_known_matrix (hm : 1≤m) (mask : Mask m) (A : Y →L[ℝ] Y)
    (θ : Leaf.Marks Y E m) (Z : Leaf.Space Y E m) :
    richJet (objective mask A θ) Z=richDecoder mask ((A,θ),Z) := by
  have hc := objectiveJoint_contDiff (Y := Y) (E := E) hm mask
  have h1 := partialFDeriv_eq (A,θ) Z (hc.differentiable (by decide : (1:WithTop ℕ∞) ≤ 3) ((A,θ),Z))
  have h2 := partialFDeriv_twice_eq hc (A,θ) Z
  exact Prod.ext rfl (Prod.ext h1.symm h2.symm)

theorem richDecoder_erasure (hm : 1≤m) (mask : Mask m) (A : Y →L[ℝ] Y)
    {θ η : Leaf.Marks Y E m} (he : view mask θ=view mask η) (Z : Leaf.Space Y E m) :
    richDecoder mask ((A,θ),Z)=richDecoder mask ((A,η),Z) := by
  rw [← richJet_known_matrix hm mask A θ Z,← richJet_known_matrix hm mask A η Z,
    objective_erasure mask A he]

variable [CompleteSpace Y]

theorem ordinaryJet_one_product (hm : 1≤m) (mask : Mask m) (A : Y →L[ℝ] Y)
    (hsym : ∀ x z,⟪A x,z⟫_ℝ=⟪x,A z⟫_ℝ) (θ : Leaf.Marks Y E m) (Z : Leaf.Space Y E m) :
    ordinaryJet (objective mask A θ) Z=
      ordinaryDecoder mask ((θ,Z),A (numerical Y E m (Inner.absoluteDepth+2) Z)) := by
  have hn := (LeafNumerical.base_hasGradientAt (M := m) (Leaf.capRadius_pos hm) A hsym
    (numerical Y E m (Inner.absoluteDepth+2) Z)).hasFDerivAt
  have hD : HasFDerivAt (LeafNumerical.base m (Leaf.capRadius m) A)
      (innerSL ℝ (Leaf.gradientFromProduct m (Leaf.capRadius m)
        (numerical Y E m (Inner.absoluteDepth+2) Z) (A (numerical Y E m (Inner.absoluteDepth+2) Z))))
      (numerical Y E m (Inner.absoluteDepth+2) Z) := by convert hn using 1
  have hd := (hD.comp Z (numerical Y E m (Inner.absoluteDepth+2)).hasFDerivAt).add
    ((knownTerm_contDiff mask θ).differentiable (by decide : (1:WithTop ℕ∞) ≤ 3) Z).hasFDerivAt
  exact Prod.ext rfl hd.fderiv

end GradientHessian.CensoredLeaf
