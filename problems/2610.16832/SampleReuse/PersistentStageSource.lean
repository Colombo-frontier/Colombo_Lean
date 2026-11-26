import SampleReuse.PersistentOptionTable
import SampleReuse.PersistentSignTableBound

/-! The single-block source used by entry resampling is exactly the source
of the stopped table experiment, with one deterministic dummy coordinate. -/

open SecondOrder
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section
variable {d : ℕ} {Handle : Type} [Fintype Handle]

local instance stageSourceDecidableEq : DecidableEq (Option Handle) := Classical.decEq _

theorem finiteProdPMF_unit_mean {B : Type} [Fintype B] (p : PMF B) (F : B × Unit → ℝ) :
    pmfMean (finiteProdPMF p (PMF.pure ())) F = pmfMean p (fun b => F (b, ())) := by
  simp [pmfMean, finiteProdPMF_apply, Fintype.sum_prod_type]

theorem sign_stage_source_mean (R : ℝ) (hR : 2 ≤ R) (a₀ : Fin d → SignedCoefficient R)
    (F : ((Fin d → Bool) × Unit) × (Option Handle → Fin d → SignedCoefficient R) → ℝ) :
    pmfMean
      (seededTablePMF (finiteProdPMF (PMF.uniformOfFintype (Fin d → Bool)) (PMF.pure ()))
        (fun s => signStageTrueArray R hR (fun r : Option Handle => r.isSome = true) (fun _ => PMF.pure a₀) s.1)) F =
      pmfMean (persistentBlockLaw d Handle R hR) (fun b => F ((b.1, ()), extendOptionTable a₀ b.2)) := by
  simp only [seededTablePMF, persistentBlockLaw, finiteConditionalPMF_mean,
    finiteProdPMF_unit_mean]
  apply pmfMean_congr
  intro θ
  have hp : finitePiPMF (signStageTrueArray R hR (fun r : Option Handle => r.isSome = true)
      (fun _ => PMF.pure a₀) θ) = optionTableLaw a₀ (fun _ : Handle => firstOrderCoefficientLaw θ R hR) := by
    unfold optionTableLaw
    congr 1
    funext r
    cases r <;> simp [signStageTrueArray]
  rw [hp]
  convert optionTableLaw_mean a₀ (fun _ : Handle => firstOrderCoefficientLaw θ R hR)
    (fun table => F ((θ, ()), table)) using 1
  congr 1
  exact Subsingleton.elim _ _

local instance stageSourceOptionMeasurable : MeasurableSpace (Option Handle) := ⊤
local instance stageSourceOptionSingleton : MeasurableSingletonClass (Option Handle) := ⟨fun _ => trivial⟩

/-- The complete target sign/table package from the original product
source obeys the same fast-activation bound, with no extra randomness. -/
theorem persistent_stage_source_fast_bound (R : ℝ) (hR : 2 ≤ R)
    (query : ∀ n, FiniteHistory Unit (Fin d → SignedCoefficient R) n → Option Handle)
    (a₀ : Fin d → SignedCoefficient R) (cap N : ℕ)
    (points : ∀ n, FiniteHistory Unit (Fin d → SignedCoefficient R) n → Point d)
    {L : ℝ} (hL : 0 < L)
    (hlog : L ≤ Real.log (1 / ((N + 1 : ℕ) * (2 * Real.exp (-(d : ℝ) / 128)))))
    (hbudget : 32 * ((cap : ℝ) * ((d : ℝ) / R ^ 2) + Real.log 2) ≤ L) :
    pmfEventProbability (persistentBlockLaw d Handle R hR)
      (fun b => decide (tableHistory (liftPublicQuery query) (b.1, ()) (extendOptionTable a₀ b.2) N ∈
        signTableFastSet query (fun r => r.isSome = true) cap points N)) ≤ 1 / 32 := by
  have hb := persistent_sign_table_fast_bound R hR query (fun r => r.isSome = true)
    (fun _ => PMF.pure a₀) a₀ cap N points hL hlog hbudget
  rw [pmfEventProbability_mean, sign_stage_source_mean] at hb
  simpa only [pmfEventProbability_mean] using hb

end
end SampleReuse
