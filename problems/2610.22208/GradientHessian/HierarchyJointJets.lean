import GradientHessian.HierarchyJointCalculus

/-! Actual physical first and second jets, continuous in every marked
coefficient before the possibly discontinuous readout assembly. -/

noncomputable section
namespace GradientHessian.HierarchyParameters
universe u
open HigherHierarchy PartialJetCalculus JetLocality

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

def richDecoder (K : ℝ) (t : ℕ) (p : Parameters Y E H m t × Space Y E H m t) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) ×
      (Space Y E H m t →L[ℝ] (Space Y E H m t →L[ℝ] ℝ)) :=
  (scalarJoint K t p, partialFDeriv (scalarJoint K t) p,
    partialFDeriv (partialFDeriv (scalarJoint K t)) p)

theorem richDecoder_continuous {K : ℝ} (hK : 0<K) (t : ℕ) :
    Continuous (richDecoder (Y := Y) (E := E) (H := H) (m := m) K t) := by
  have hc := scalarJoint_contDiff (Y := Y) (E := E) (H := H) (m := m) hK t
  have h1 := partialFDeriv_contDiff hc (by decide : (2:WithTop ℕ∞)+1 ≤ 3)
  have h2 := partialFDeriv_contDiff h1 (by decide : (1:WithTop ℕ∞)+1 ≤ 2)
  exact hc.continuous.prodMk (h1.continuous.prodMk h2.continuous)

theorem richJet_decode {K : ℝ} (hK : 0<K) (t : ℕ)
    (p : Parameters Y E H m t) (Z : Space Y E H m t) :
    richJet (scalar K t (decode t p)) Z = richDecoder K t (p,Z) := by
  have hc := scalarJoint_contDiff (Y := Y) (E := E) (H := H) (m := m) hK t
  have h1 := partialFDeriv_eq p Z (hc.differentiable (by decide : (1:WithTop ℕ∞) ≤ 3) (p,Z))
  have h2 := partialFDeriv_twice_eq hc p Z
  exact Prod.ext rfl (Prod.ext h1.symm h2.symm)

def ordinaryDecoder (K : ℝ) (t : ℕ) (p : Parameters Y E H m t × Space Y E H m t) :
    ℝ × (Space Y E H m t →L[ℝ] ℝ) :=
  (scalarJoint K t p, partialFDeriv (scalarJoint K t) p)

theorem ordinaryDecoder_continuous {K : ℝ} (hK : 0<K) (t : ℕ) :
    Continuous (ordinaryDecoder (Y := Y) (E := E) (H := H) (m := m) K t) := by
  have hc := scalarJoint_contDiff (Y := Y) (E := E) (H := H) (m := m) hK t
  have h1 := partialFDeriv_contDiff hc (by decide : (2:WithTop ℕ∞)+1 ≤ 3)
  exact hc.continuous.prodMk h1.continuous

theorem ordinaryJet_decode {K : ℝ} (hK : 0<K) (t : ℕ)
    (p : Parameters Y E H m t) (Z : Space Y E H m t) :
    ordinaryJet (scalar K t (decode t p)) Z = ordinaryDecoder K t (p,Z) := by
  have hc := scalarJoint_contDiff (Y := Y) (E := E) (H := H) (m := m) hK t
  exact Prod.ext rfl (partialFDeriv_eq p Z
    (hc.differentiable (by decide : (1:WithTop ℕ∞) ≤ 3) (p,Z))).symm

end GradientHessian.HierarchyParameters
