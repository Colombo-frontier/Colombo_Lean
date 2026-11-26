import GradientHessian.JointMarkedCalculus

/-! Jointly Borel ordinary and rich decoders in every raw finite marked
coefficient. Physical derivatives are partial derivatives of the literal
joint scalar, not additional fields supplied to a decoder. -/

noncomputable section
namespace GradientHessian.PartialJetCalculus

variable {P F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]

def partialFDeriv (H : P × F → V) (p : P × F) : F →L[ℝ] V :=
  (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ P F)

theorem partialFDeriv_eq {H : P × F → V} (p : P) (x : F) (hH : DifferentiableAt ℝ H (p,x)) :
    partialFDeriv H (p,x) = fderiv ℝ (fun y => H (p,y)) x :=
  (hH.hasFDerivAt.comp x (hasFDerivAt_prodMk_right p x)).fderiv.symm

theorem partialFDeriv_contDiff {H : P × F → V} {n N : WithTop ℕ∞} (hH : ContDiff ℝ N H)
    (hn : n+1 ≤ N) : ContDiff ℝ n (partialFDeriv H) :=
  (hH.fderiv_right hn).clm_comp contDiff_const

theorem partialFDeriv_twice_eq {H : P × F → V} (hH : ContDiff ℝ 3 H) (p : P) (x : F) :
    partialFDeriv (partialFDeriv H) (p,x) = fderiv ℝ (fderiv ℝ (fun y => H (p,y))) x := by
  have hfirst := partialFDeriv_contDiff hH (by decide : (2:WithTop ℕ∞)+1 ≤ 3)
  have h := partialFDeriv_eq p x (hfirst.differentiable (by decide : (1:WithTop ℕ∞) ≤ 2) (p,x))
  have he : (fun y => partialFDeriv H (p,y)) = fderiv ℝ (fun y => H (p,y)) := by
    funext y
    exact partialFDeriv_eq p y (hH.differentiable (by decide : (1:WithTop ℕ∞) ≤ 3) (p,y))
  rwa [he] at h

end GradientHessian.PartialJetCalculus

namespace GradientHessian.Leaf
open InnerCoordinates PartialJetCalculus JetLocality
open scoped InnerProductSpace

variable (Y E : Type*) [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Marks (m : ℕ) := (Fin m → Y) × (Fin m → Y) × (Fin m → Fin (Inner.absoluteDepth+2) → E)
abbrev MatrixMarks (m : ℕ) := (Y →L[ℝ] Y) × Marks Y E m

variable {Y E} {m : ℕ}

def knownTermJoint (p : Marks Y E m × Space Y E m) : ℝ :=
  knownTerm p.1.1 p.1.2.1 p.1.2.2 p.2

theorem knownTerm_joint_contDiff : ContDiff ℝ 3 (knownTermJoint (Y := Y) (E := E) (m := m)) :=
  JointMarkedCalculus.knownTerm_contDiff (fun _ => by fun_prop) (fun _ => by fun_prop)
    (fun _ _ => by fun_prop) contDiff_snd

theorem knownTerm_partial_fderiv (θ : Marks Y E m) (Z : Space Y E m) :
    fderiv ℝ (knownTerm θ.1 θ.2.1 θ.2.2) Z =
      (fderiv ℝ knownTermJoint (θ,Z)).comp (ContinuousLinearMap.inr ℝ (Marks Y E m) (Space Y E m)) :=
  (partialFDeriv_eq θ Z (knownTerm_joint_contDiff.differentiable
    (by decide : (1:WithTop ℕ∞) ≤ 3) (θ,Z))).symm

theorem knownTerm_partial_continuous :
    Continuous (fun p : Marks Y E m × Space Y E m => fderiv ℝ (knownTerm p.1.1 p.1.2.1 p.1.2.2) p.2) := by
  have he : (fun p : Marks Y E m × Space Y E m => fderiv ℝ (knownTerm p.1.1 p.1.2.1 p.1.2.2) p.2) =
      partialFDeriv knownTermJoint := funext (fun p => knownTerm_partial_fderiv p.1 p.2)
  rw [he]
  exact (partialFDeriv_contDiff knownTerm_joint_contDiff (by decide : (2:WithTop ℕ∞)+1 ≤ 3)).continuous

def markedOrdinaryDecoder (p : (Marks Y E m × Space Y E m) × Y) :
    ℝ × (Space Y E m →L[ℝ] ℝ) :=
  ordinaryDecoder p.1.1.1 p.1.1.2.1 p.1.1.2.2 (p.1.2,p.2)

theorem markedOrdinaryDecoder_continuous (hm : 1 ≤ m) :
    Continuous (markedOrdinaryDecoder (Y := Y) (E := E) (m := m)) := by
  have hp : Continuous (fun p : (Marks Y E m × Space Y E m) × Y =>
      (numerical Y E m (Inner.absoluteDepth+2) p.1.2,p.2)) :=
    ((numerical Y E m (Inner.absoluteDepth+2)).continuous.comp
      (continuous_snd.comp continuous_fst)).prodMk continuous_snd
  have hval := ((valueFromProduct_continuous (m:ℝ) (capRadius_pos hm)).comp hp).add
    (knownTerm_joint_contDiff.continuous.comp continuous_fst)
  have hgrad := (gradientFromProduct_continuous (m:ℝ) (capRadius_pos hm)).comp hp
  have hcov := ((innerSL ℝ : Y →L[ℝ] Y →L[ℝ] ℝ).continuous.comp hgrad).clm_comp
    (continuous_const : Continuous (fun _ : (Marks Y E m × Space Y E m) × Y =>
      numerical Y E m (Inner.absoluteDepth+2)))
  exact hval.prodMk (hcov.add (knownTerm_partial_continuous.comp continuous_fst))

theorem markedOrdinaryDecoder_borel (hm : 1 ≤ m) :
    @Measurable ((Marks Y E m × Space Y E m) × Y) (ℝ × (Space Y E m →L[ℝ] ℝ))
      (borel _) (borel _) (markedOrdinaryDecoder (Y := Y) (E := E)) :=
  (markedOrdinaryDecoder_continuous (Y := Y) (E := E) hm).borel_measurable

theorem markedOrdinaryDecoder_measurable
    [MeasurableSpace (Marks Y E m)] [BorelSpace (Marks Y E m)]
    [MeasurableSpace (Space Y E m)] [BorelSpace (Space Y E m)] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology (Marks Y E m)] [SecondCountableTopology (Space Y E m)] [SecondCountableTopology Y]
    (hm : 1 ≤ m) :
    @Measurable ((Marks Y E m × Space Y E m) × Y) (ℝ × (Space Y E m →L[ℝ] ℝ))
      inferInstance (borel _) (markedOrdinaryDecoder (Y := Y) (E := E)) :=
  (markedOrdinaryDecoder_borel (Y := Y) (E := E) hm).mono OpensMeasurableSpace.borel_le le_rfl

def objectiveJoint (p : MatrixMarks Y E m × Space Y E m) : ℝ :=
  objective p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2

theorem objective_joint_contDiff (hm : 1 ≤ m) :
    ContDiff ℝ 3 (objectiveJoint (Y := Y) (E := E) (m := m)) :=
  JointMarkedCalculus.objective_contDiff hm (by fun_prop) (fun _ => by fun_prop)
    (fun _ => by fun_prop) (fun _ _ => by fun_prop) contDiff_snd

/-- A rich decoder on every raw matrix and mark input, including nonsymmetric
matrices and nonunit marks. It uses actual partial physical derivatives. -/
def markedRichDecoder (p : MatrixMarks Y E m × Space Y E m) :
    ℝ × (Space Y E m →L[ℝ] ℝ) × (Space Y E m →L[ℝ] (Space Y E m →L[ℝ] ℝ)) :=
  (objectiveJoint p, partialFDeriv objectiveJoint p, partialFDeriv (partialFDeriv objectiveJoint) p)

theorem markedRichDecoder_continuous (hm : 1 ≤ m) :
    Continuous (markedRichDecoder (Y := Y) (E := E) (m := m)) := by
  have hc := objective_joint_contDiff (Y := Y) (E := E) hm
  have h1 := partialFDeriv_contDiff hc (by decide : (2:WithTop ℕ∞)+1 ≤ 3)
  have h2 := partialFDeriv_contDiff h1 (by decide : (1:WithTop ℕ∞)+1 ≤ 2)
  exact hc.continuous.prodMk (h1.continuous.prodMk h2.continuous)

theorem markedRichDecoder_borel (hm : 1 ≤ m) :
    @Measurable (MatrixMarks Y E m × Space Y E m)
      (ℝ × (Space Y E m →L[ℝ] ℝ) × (Space Y E m →L[ℝ] (Space Y E m →L[ℝ] ℝ)))
      (borel _) (borel _) (markedRichDecoder (Y := Y) (E := E)) :=
  (markedRichDecoder_continuous (Y := Y) (E := E) hm).borel_measurable

theorem markedRichDecoder_measurable
    [MeasurableSpace (MatrixMarks Y E m)] [BorelSpace (MatrixMarks Y E m)]
    [MeasurableSpace (Space Y E m)] [BorelSpace (Space Y E m)]
    [SecondCountableTopology (MatrixMarks Y E m)] [SecondCountableTopology (Space Y E m)] (hm : 1 ≤ m) :
    @Measurable (MatrixMarks Y E m × Space Y E m)
      (ℝ × (Space Y E m →L[ℝ] ℝ) × (Space Y E m →L[ℝ] (Space Y E m →L[ℝ] ℝ)))
      inferInstance (borel _) (markedRichDecoder (Y := Y) (E := E)) :=
  (markedRichDecoder_borel (Y := Y) (E := E) hm).mono OpensMeasurableSpace.borel_le le_rfl

theorem richJet_marked_decoder (hm : 1 ≤ m) (A : Y →L[ℝ] Y) (θ : Marks Y E m) (Z : Space Y E m) :
    richJet (objective A θ.1 θ.2.1 θ.2.2) Z = markedRichDecoder ((A,θ),Z) := by
  have hc := objective_joint_contDiff (Y := Y) (E := E) hm
  have h1 := partialFDeriv_eq (A,θ) Z (hc.differentiable (by decide : (1:WithTop ℕ∞) ≤ 3) ((A,θ),Z))
  have h2 := partialFDeriv_twice_eq hc (A,θ) Z
  exact Prod.ext rfl (Prod.ext h1.symm h2.symm)

variable [CompleteSpace Y]

theorem ordinaryJet_marked_decoder (hm : 1 ≤ m) (A : Y →L[ℝ] Y)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (θ : Marks Y E m) (Z : Space Y E m) :
    ordinaryJet (objective A θ.1 θ.2.1 θ.2.2) Z =
      markedOrdinaryDecoder ((θ,Z),A (numerical Y E m (Inner.absoluteDepth+2) Z)) :=
  ordinaryJet_one_product hm A hsym θ.1 θ.2.1 θ.2.2 Z

theorem markedRichDecoder_eq_knownMatrixDecoder (hm : 1 ≤ m) (A : Y →L[ℝ] Y)
    (hsym : ∀ x z, ⟪A x,z⟫_ℝ = ⟪x,A z⟫_ℝ) (θ : Marks Y E m) (Z : Space Y E m) :
    markedRichDecoder ((A,θ),Z) = knownMatrixDecoder A θ.1 θ.2.1 θ.2.2 Z :=
  (richJet_marked_decoder hm A θ Z).symm.trans (richJet_known_matrix hm A hsym θ.1 θ.2.1 θ.2.2 Z)

end GradientHessian.Leaf
