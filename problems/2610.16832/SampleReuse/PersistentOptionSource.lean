import SampleReuse.PersistentOptionTable

open SecondOrder
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section
variable {B Key A : Type} [Fintype B] [Fintype Key] [Fintype A]

local instance optionSourceDecidableEq : DecidableEq (Option Key) := Classical.decEq _

theorem optionSource_unit_mean (p : PMF B) (F : B × Unit → ℝ) :
    pmfMean (finiteProdPMF p (PMF.pure ())) F = pmfMean p (fun b => F (b, ())) := by
  simp [pmfMean, finiteProdPMF_apply, Fintype.sum_prod_type]

theorem optionSource_mean (ρ : PMF B) (p : B → Key → PMF A) (a₀ : A)
    (F : (B × Unit) × (Option Key → A) → ℝ) :
    pmfMean (seededTablePMF (finiteProdPMF ρ (PMF.pure ()))
      (fun s r => match r with | none => PMF.pure a₀ | some k => p s.1 k)) F =
    pmfMean (finiteConditionalPMF ρ (fun b => finitePiPMF (p b)))
      (fun w => F ((w.1, ()), extendOptionTable a₀ w.2)) := by
  simp only [seededTablePMF, finiteConditionalPMF_mean, optionSource_unit_mean]
  apply pmfMean_congr
  intro b
  convert optionTableLaw_mean a₀ (p b) (fun table => F ((b, ()), table)) using 1
  congr 1
  exact Subsingleton.elim _ _

end
end SampleReuse
