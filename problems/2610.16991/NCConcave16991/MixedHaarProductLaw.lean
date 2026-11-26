import Mathlib.MeasureTheory.Constructions.Pi

/-! # Exact finite-vertex lifting of genuine one-coordinate joint laws -/

noncomputable section

open Set MeasureTheory Measure

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

variable {I : Type*} [Fintype I] {W Z : I → Type*}
  [∀ i, MeasurableSpace (W i)] [∀ i, MeasurableSpace (Z i)]

def dependentSplit : (∀ i, W i × Z i) ≃ᵐ (∀ i, W i) × (∀ i, Z i) where
  toFun f := (fun i ↦ (f i).1,fun i ↦ (f i).2)
  invFun p := fun i ↦ (p.1 i,p.2 i)
  left_inv f := by funext i; rfl
  right_inv p := rfl
  measurable_toFun :=
    (measurable_pi_iff.mpr (fun i ↦ measurable_fst.comp (measurable_pi_apply i))).prodMk
      (measurable_pi_iff.mpr (fun i ↦ measurable_snd.comp (measurable_pi_apply i)))
  measurable_invFun := measurable_pi_iff.mpr (fun i ↦
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem dependentSplit_preserving (τ : ∀ i, Measure (W i)) (ν : ∀ i, Measure (Z i))
    [∀ i, IsProbabilityMeasure (τ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    MeasurePreserving (dependentSplit (W := W) (Z := Z))
      (Measure.pi (fun i ↦ (τ i).prod (ν i))) ((Measure.pi τ).prod (Measure.pi ν)) := by
  refine ⟨dependentSplit.measurable,?_⟩
  refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
    ((FiniteSpanningSetsIn.pi fun i ↦ (τ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi fun i ↦ (ν i).toFiniteSpanningSetsIn)) ?_).symm
  · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
    · exact (FiniteSpanningSetsIn.pi fun i ↦ (τ i).toFiniteSpanningSetsIn).isCountablySpanning
    · exact (FiniteSpanningSetsIn.pi fun i ↦ (ν i).toFiniteSpanningSetsIn).isCountablySpanning
  · rintro A ⟨s,⟨s,_,rfl⟩,⟨t,⟨t,_,rfl⟩,rfl⟩⟩
    rw [MeasurableEquiv.map_apply]
    have he : (dependentSplit (W := W) (Z := Z)) ⁻¹' (univ.pi s ×ˢ univ.pi t) =
        univ.pi (fun i ↦ s i ×ˢ t i) := by
      ext f
      simp only [mem_preimage,mem_prod,mem_pi,mem_univ,true_implies,dependentSplit,
        MeasurableEquiv.coe_mk]
      exact forall_and.symm
    rw [he]
    simp_rw [pi_pi,prod_prod,pi_pi,Finset.prod_mul_distrib]

theorem dependentSplit_symm_preserving (τ : ∀ i, Measure (W i)) (ν : ∀ i, Measure (Z i))
    [∀ i, IsProbabilityMeasure (τ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    MeasurePreserving (dependentSplit (W := W) (Z := Z)).symm
      ((Measure.pi τ).prod (Measure.pi ν)) (Measure.pi (fun i ↦ (τ i).prod (ν i))) := by
  let e := dependentSplit (W := W) (Z := Z)
  have hp := dependentSplit_preserving τ ν
  refine ⟨e.symm.measurable,?_⟩
  have hh := congrArg (fun μ ↦ μ.map e.symm) hp.map_eq
  rw [Measure.map_map e.symm.measurable e.measurable] at hh
  simpa only [e.symm_comp_self,Measure.map_id] using hh.symm

theorem independent_joint_laws {A B : I → Type*}
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]
    (τ : ∀ i, Measure (W i)) (ν : ∀ i, Measure (Z i))
    [∀ i, IsProbabilityMeasure (τ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (f : ∀ i, W i × Z i → A i × B i) (g : ∀ i, Z i → A i × B i)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hlocal : ∀ i, ((τ i).prod (ν i)).map (f i) = (ν i).map (g i)) :
    ((Measure.pi τ).prod (Measure.pi ν)).map
        (fun p ↦ (fun i ↦ (f i (p.1 i,p.2 i)).1,fun i ↦ (f i (p.1 i,p.2 i)).2)) =
      (Measure.pi ν).map (fun z ↦ (fun i ↦ (g i (z i)).1,fun i ↦ (g i (z i)).2)) := by
  have hpi : (Measure.pi (fun i ↦ (τ i).prod (ν i))).map (fun x i ↦ f i (x i)) =
      (Measure.pi ν).map (fun z i ↦ g i (z i)) := by
    rw [pi_map_pi (fun i ↦ (hf i).aemeasurable),pi_map_pi (fun i ↦ (hg i).aemeasurable)]
    simp_rw [hlocal]
  let output := dependentSplit (W := A) (Z := B)
  have heq := congrArg (fun μ ↦ μ.map output) hpi
  have hfp : Measurable (fun x : ∀ i, W i × Z i ↦ fun i ↦ f i (x i)) :=
    measurable_pi_iff.mpr (fun i ↦ (hf i).comp (measurable_pi_apply i))
  have hgp : Measurable (fun z : ∀ i, Z i ↦ fun i ↦ g i (z i)) :=
    measurable_pi_iff.mpr (fun i ↦ (hg i).comp (measurable_pi_apply i))
  rw [Measure.map_map output.measurable hfp,Measure.map_map output.measurable hgp] at heq
  let input := dependentSplit (W := W) (Z := Z)
  have hin := dependentSplit_preserving τ ν
  have hresult : Measurable (fun p : (∀ i, W i) × (∀ i, Z i) ↦
      (fun i ↦ (f i (p.1 i,p.2 i)).1,fun i ↦ (f i (p.1 i,p.2 i)).2)) :=
    (measurable_pi_iff.mpr (fun i ↦ measurable_fst.comp
      ((hf i).comp (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))))).prodMk
    (measurable_pi_iff.mpr (fun i ↦ measurable_snd.comp
      ((hf i).comp (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)))))
  rw [← hin.map_eq,Measure.map_map hresult input.measurable]
  exact heq

theorem independent_joint_laws_regrouped {X A B : I → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]
    (ξ : ∀ i, Measure (X i)) (τ : ∀ i, Measure (W i)) (ν : ∀ i, Measure (Z i))
    [∀ i, IsProbabilityMeasure (ξ i)] [∀ i, IsProbabilityMeasure (τ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (f : ∀ i, (X i × W i) × Z i → A i × B i) (g : ∀ i, Z i → A i × B i)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hlocal : ∀ i, (((ξ i).prod (τ i)).prod (ν i)).map (f i) = (ν i).map (g i)) :
    (((Measure.pi ξ).prod (Measure.pi τ)).prod (Measure.pi ν)).map
        (fun p ↦ (fun i ↦ (f i ((p.1.1 i,p.1.2 i),p.2 i)).1,
          fun i ↦ (f i ((p.1.1 i,p.1.2 i),p.2 i)).2)) =
      (Measure.pi ν).map (fun z ↦ (fun i ↦ (g i (z i)).1,fun i ↦ (g i (z i)).2)) := by
  have hh := independent_joint_laws (fun i ↦ (ξ i).prod (τ i)) ν f g hf hg hlocal
  have hin := (dependentSplit_symm_preserving ξ τ).prod (MeasurePreserving.id (Measure.pi ν))
  have hF : Measurable (fun p : (∀ i, X i × W i) × (∀ i, Z i) ↦
      (fun i ↦ (f i (p.1 i,p.2 i)).1,fun i ↦ (f i (p.1 i,p.2 i)).2)) :=
    (measurable_pi_iff.mpr (fun i ↦ measurable_fst.comp
      ((hf i).comp (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))))).prodMk
    (measurable_pi_iff.mpr (fun i ↦ measurable_snd.comp
      ((hf i).comp (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)))))
  rw [← hin.map_eq,Measure.map_map hF hin.measurable] at hh
  exact hh

end NCConcave16991.MixedHaar
