import Geode.ArchiveCompletion
import Geode.StateBudget

/-! A single fixed instance defeats any prescribed output after a legal prefix. -/
namespace Geode.Lorentz

open Geode.OracleReplay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {o : Point E} {R L ε : ℝ}

theorem ArchiveValid.bad_output_completion {s : PublicState o R (4 * ε)}
    {history : History (Point E) (FirstOrderReply E)} (h : ArchiveValid s history L)
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (hk : s.cuts ≤ Geode.queryHorizon R ε)
    (hdim : Geode.queryHorizon R ε + 3 ≤ Module.finrank ℝ (Ambient E)) (x : Point E) :
    ∃ (f : Point E → ℝ) (O : Point E → FirstOrderReply E) (p : Point E),
      AdmissibleObjective o R L f ∧ LegalOracle f O ∧
      (∀ y, (∀ z, f y ≤ f z) ↔ y = p) ∧ f p = 0 ∧ dist o p = R ∧
      (∀ y r, (y, r) ∈ history → O y = r) ∧ 2 * ε * L * R ≤ f x - f p := by
  obtain ⟨p, hp, hfar⟩ := s.output_separation hR hε hεmax hk hdim x
  have hμ : 0 < 4 * ε := by positivity
  have hμ1 : 4 * ε < 1 := by linarith
  obtain ⟨f, O, hf, hO, hmin, hzero, hfloor, hagree⟩ := h.complete hp hL hμ hμ1
  refine ⟨f, O, p, hf, hO, hmin, hzero, s.original p hp, hagree, ?_⟩
  have hprod := mul_le_mul_of_nonneg_left hfar (show 0 ≤ L * (4 * ε) by positivity)
  have hlower := hfloor x
  rw [hzero]
  nlinarith

end Geode.Lorentz
