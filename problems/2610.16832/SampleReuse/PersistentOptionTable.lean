import SampleReuse.PersistentSourceLaw
import SampleReuse.PersistentSeededTable

/-! Adding the deterministic dummy key used for lower-index stage replies
preserves the law of every real handle's preallocated target array. -/

open SecondOrder
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section
variable {Handle A : Type} [Fintype Handle] [Fintype A]

def extendOptionTable (a₀ : A) (table : Handle → A) : Option Handle → A
  | none => a₀
  | some r => table r

def optionTableLaw (a₀ : A) (p : Handle → PMF A) : PMF (Option Handle → A) :=
  finitePiPMF (fun r => match r with | none => PMF.pure a₀ | some r => p r)

theorem optionTableLaw_mean (a₀ : A) (p : Handle → PMF A) (F : (Option Handle → A) → ℝ) :
    pmfMean (optionTableLaw a₀ p) F =
      pmfMean (finitePiPMF p) (fun table => F (extendOptionTable a₀ table)) := by
  unfold pmfMean
  rw [← Equiv.sum_comp (Equiv.piOptionEquivProd (β := fun _ : Option Handle => A)).symm]
  simp only [optionTableLaw, finitePiPMF_apply, Fintype.prod_option, ENNReal.toReal_mul,
    Fintype.sum_prod_type, Equiv.piOptionEquivProd, Equiv.coe_fn_symm_mk]
  simp [PMF.pure_apply, apply_ite ENNReal.toReal, extendOptionTable, ENNReal.toReal_prod, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (fun y => (∏ i, ((p i) (x i)).toReal) * F y)
  funext a
  cases a <;> rfl

theorem optionTableLaw_eq_map (a₀ : A) (p : Handle → PMF A) :
    optionTableLaw a₀ p = (finitePiPMF p).map (extendOptionTable a₀) := by
  ext w
  apply (ENNReal.toReal_eq_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [finite_pmf_map_toReal]
  have hh := optionTableLaw_mean a₀ p (fun v => if v = w then (1 : ℝ) else 0)
  simpa [pmfMean, smul_eq_mul] using hh

end
end SampleReuse
