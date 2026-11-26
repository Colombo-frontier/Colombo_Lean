import SampleReuse.PersistentBlockSource

/-! Exact reordering of the finite source law: independent block packages
equal an independent hidden prior followed by iid persistent full-loss
sample tables. This identifies the resampling law with the manuscript. -/

open SecondOrder
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle : Type} [Fintype Handle]

def persistentSourceEquiv (d T : ℕ) (Handle : Type) (R : ℝ) :
    (Fin (T + 1) → PersistentBlock d Handle R) ≃
      ((Fin (T + 1) → Fin d → Bool) × (Handle → FirstOrderCoefficients d T R)) where
  toFun w := (persistentSourceHidden w, persistentSourceTable w)
  invFun w := fun i => (w.1 i, fun r => w.2 r i)
  left_inv w := by funext i; exact Prod.eta (w i)
  right_inv w := rfl

def persistentOriginalJointLaw (d T : ℕ) (Handle : Type) [Fintype Handle] (R : ℝ) (hR : 2 ≤ R) :
    PMF ((Fin (T + 1) → Fin d → Bool) × (Handle → FirstOrderCoefficients d T R)) :=
  finiteConditionalPMF (finitePiPMF (fun _ : Fin (T + 1) => PMF.uniformOfFintype (Fin d → Bool)))
    (fun Θ => finitePiPMF (fun _ : Handle => firstOrderChainCoefficientLaw Θ R hR))

theorem pmf_map_equiv_apply {B C : Type*} (p : PMF B) (e : B ≃ C) (c : C) :
    p.map e c = p (e.symm c) := by
  rw [PMF.map_apply]
  rw [tsum_eq_single (e.symm c)]
  · simp
  · intro b hb
    have hn : c ≠ e b := by
      intro he
      apply hb
      exact e.injective (by simpa using he.symm)
    simp only [if_neg hn]

/-- Each handle is sampled once from the actual full scalar-loss law;
rearranging its independent blocks changes no joint distribution. -/
theorem persistent_source_eq_original (R : ℝ) (hR : 2 ≤ R) :
    (persistentSourceLaw d T Handle R hR).map (persistentSourceEquiv d T Handle R) =
      persistentOriginalJointLaw d T Handle R hR := by
  ext w
  rw [pmf_map_equiv_apply]
  simp only [persistentSourceLaw, persistentBlockLaw, persistentOriginalJointLaw,
    finitePiPMF_apply, finiteConditionalPMF_apply, persistentSourceEquiv, Equiv.coe_fn_symm_mk,
    firstOrderChainCoefficientLaw, Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_comm

end
end SampleReuse
