import NCConcave16991.MixedHaarFrameStep
import NCConcave16991.MixedHaarFrameSafeStep
import NCConcave16991.BranchOracleLedger

/-! # Actual frame births transported to the native formal layer -/

namespace NCConcave16991.BranchOracle
noncomputable section
open MixedHaar

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {k : ℕ} (C : F ≃ₗᵢ[ℝ] Space k)

def nativePartialDomain (s : FrameState k) : Submodule ℝ F :=
  (frameDomain s).map C.symm.toLinearMap

def nativeFrameRequest (q : F ⊕ F) : FrameRequest k := q.map C C

def nativeFrameStep (s : FrameState k) (q : F ⊕ F) (g : F) : FrameState k × F :=
  let a := frameStep s (nativeFrameRequest C q) (C g)
  (a.1, C.symm a.2)

def nativeFrameBirth (q : F ⊕ F) (g : F) : F := q.elim id (fun _ ↦ g)

def nativeSafeFrameStep (s : FrameState k) (q : F ⊕ F) (g : F) : FrameState k × F :=
  let a := frameSafeStep s (nativeFrameRequest C q) (C g)
  (a.1, C.symm a.2)

theorem nativeFrameStep_domain_le (s : FrameState k) (q : F ⊕ F) (g : F)
    (hlegal : FrameStepLegal s (nativeFrameRequest C q) (C g)) :
    nativePartialDomain C (nativeFrameStep C s q g).1 ≤
      nativePartialDomain C s ⊔ Submodule.span ℝ ({nativeFrameBirth q g} : Set F) := by
  have hh : (frameDomain (frameStep s (nativeFrameRequest C q) (C g)).1).map C.symm.toLinearMap ≤
      (frameDomain s ⊔ Submodule.span ℝ ({frameStepBirth (nativeFrameRequest C q) (C g)} : Set (Space k))).map C.symm.toLinearMap :=
    Submodule.map_mono (frameStep_domain_le s _ _ hlegal)
  rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton] at hh
  have he : C.symm (frameStepBirth (nativeFrameRequest C q) (C g)) = nativeFrameBirth q g := by
    cases q <;> simp only [nativeFrameRequest, Sum.map_inl, Sum.map_inr, frameStepBirth,
      Sum.elim_inl, Sum.elim_inr, nativeFrameBirth, id_eq, LinearIsometryEquiv.symm_apply_apply]
  change nativePartialDomain C (nativeFrameStep C s q g).1 ≤
    nativePartialDomain C s ⊔ Submodule.span ℝ ({C.symm (frameStepBirth (nativeFrameRequest C q) (C g))} : Set F) at hh
  rw [he] at hh
  exact hh

theorem nativeInverseAnswer_mem_old_sup_gaussian (s : FrameState k) (b g : F) :
    (nativeFrameStep C s (Sum.inr b) g).2 ∈ nativePartialDomain C s ⊔ Submodule.span ℝ ({g} : Set F) := by
  have hh : C.symm (frameCandidate s (C b) (C g)) ∈
      (frameDomain s ⊔ Submodule.span ℝ ({C g} : Set (Space k))).map C.symm.toLinearMap :=
    ⟨frameCandidate s (C b) (C g), frameCandidate_mem_old_sup_gaussian s (C b) (C g), rfl⟩
  rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton] at hh
  change C.symm (frameCandidate s (C b) (C g)) ∈
    nativePartialDomain C s ⊔ Submodule.span ℝ ({C.symm (C g)} : Set F) at hh
  rw [LinearIsometryEquiv.symm_apply_apply] at hh
  exact hh

theorem nativeSafeFrameStep_domain_le (s : FrameState k) (q : F ⊕ F) (g : F) :
    nativePartialDomain C (nativeSafeFrameStep C s q g).1 ≤
      nativePartialDomain C s ⊔ Submodule.span ℝ ({nativeFrameBirth q g} : Set F) := by
  have hh : (frameDomain (frameSafeStep s (nativeFrameRequest C q) (C g)).1).map C.symm.toLinearMap ≤
      (frameDomain s ⊔ Submodule.span ℝ ({frameStepBirth (nativeFrameRequest C q) (C g)} : Set (Space k))).map C.symm.toLinearMap :=
    Submodule.map_mono (frameSafeStep_domain_le s _ _)
  rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton] at hh
  have he : C.symm (frameStepBirth (nativeFrameRequest C q) (C g)) = nativeFrameBirth q g := by
    cases q <;> simp only [nativeFrameRequest, Sum.map_inl, Sum.map_inr, frameStepBirth,
      Sum.elim_inl, Sum.elim_inr, nativeFrameBirth, id_eq, LinearIsometryEquiv.symm_apply_apply]
  change nativePartialDomain C (nativeSafeFrameStep C s q g).1 ≤
    nativePartialDomain C s ⊔ Submodule.span ℝ ({C.symm (frameStepBirth (nativeFrameRequest C q) (C g))} : Set F) at hh
  rw [he] at hh
  exact hh

theorem nativeSafeInverseAnswer_mem_old_sup_gaussian (s : FrameState k) (b g : F) :
    (nativeSafeFrameStep C s (Sum.inr b) g).2 ∈ nativePartialDomain C s ⊔ Submodule.span ℝ ({g} : Set F) := by
  change C.symm (frameSafeStep s (nativeFrameRequest C (Sum.inr b)) (C g)).2 ∈ _
  rw [frameSafeStep_reply]
  exact nativeInverseAnswer_mem_old_sup_gaussian C s b g

variable [MeasurableSpace F] [BorelSpace F]

theorem nativeFrameStep_measurable : Measurable
    (fun a : FrameState k × ((F ⊕ F) × F) ↦ nativeFrameStep C a.1 a.2.1 a.2.2) := by
  have hq : Measurable (nativeFrameRequest C) := C.continuous.measurable.sumMap C.continuous.measurable
  have hi : Measurable (fun a : FrameState k × ((F ⊕ F) × F) ↦
      (a.1, (nativeFrameRequest C a.2.1, C a.2.2))) :=
    measurable_fst.prodMk ((hq.comp (measurable_fst.comp measurable_snd)).prodMk
      (C.continuous.measurable.comp (measurable_snd.comp measurable_snd)))
  have hs := frameStep_measurable.comp hi
  convert hs.fst.prodMk (C.symm.continuous.measurable.comp hs.snd) using 1
  funext a
  rfl

end
end NCConcave16991.BranchOracle
