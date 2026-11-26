import Geode.GeneralSubgradient
import Geode.ArchiveCompletion

/-! The manuscript's canonical minimum-norm fallback at every unqueried
point, while preserving the full selected replies already in the archive. -/
namespace Geode.Lorentz

open Geode.OracleReplay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {o : Point E} {R μ L : ℝ}

theorem ArchiveValid.complete_canonical {s : PublicState o R μ}
    {history : History (Point E) (FirstOrderReply E)} (h : ArchiveValid s history L)
    {p : Point E} (hp : p ∈ s.candidates) (hL : 0 ≤ L) (hμ : 0 < μ) (hμ1 : μ < 1) :
    ∃ O : Point E → FirstOrderReply E,
      LegalOracle (completionObjective s p L) O ∧
      (∀ x r, (x, r) ∈ history → O x = r) ∧
      (∀ x, (∀ r, (x, r) ∉ history) → ∀ v,
        IsSubgradient (completionObjective s p L) x v → tangentNorm (O x).2 ≤ tangentNorm v) := by
  have hf := completionObjective_admissible s hp hL hμ hμ1
  let fallback := canonicalOracle hf.convex hL hf.lipschitz
  have hfallback : LegalOracle (completionObjective s p L) fallback :=
    canonicalOracle_legal hf.convex hL hf.lipschitz
  have harchive : ∀ x r, (x, r) ∈ history →
      r.1 = completionObjective s p L x ∧ IsSubgradient (completionObjective s p L) x r.2 := by
    intro x r hr
    obtain ⟨a, rfl, rfl, ha⟩ := h.2 x r hr
    exact ha.realizes_reply hp hL hμ.le hμ1.le
  refine ⟨cachedOracle history fallback,
    cachedOracle_legal history fallback _ harchive hfallback,
    fun x r hr => cachedOracle_realizes history fallback h.1 hr, ?_⟩
  intro x hx v hv
  rw [cachedOracle_unqueried history fallback hx]
  exact canonicalOracle_minimum_norm hf.convex hL hf.lipschitz x v hv

end Geode.Lorentz
