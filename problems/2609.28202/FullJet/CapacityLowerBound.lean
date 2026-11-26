import FullJet.ScaledChainProtocol
import FullJet.ScaleParameters
import FullJet.DimensionBudget

open MeasureTheory

universe u v

namespace FullJet

/-- With a feasible stage count and row budget, a finite dimension supports
an admissible instance whose actual output gradient exceeds the requested
accuracy. The dimension is selected before the algorithm. -/
theorem chain_capacity_lower_bound {Ω : Type u} [MeasurableSpace Ω]
    {n k m T p N q : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (hbalance : 2 * k = n + m) (hp : 2 ≤ p)
    (Δ L ε : ℝ) (hΔ : 0 < Δ) (hL : 0 < L) (hε : 0 < ε)
    (hT : (T + 1 : ℕ) ≤ chainStageCapacity p Δ L ((m : ℝ) / n) ε)
    (hbudget : 8 * (m : ℝ) + 9 * (q + 1 : ℕ) ≤ n) (hN : 2 * N ≤ (q + 1) * (T + 1))
    (hqueries : (q + 1 : ℕ) * ((m : ℝ) / n) ^ 2 ≤ (5 / 32 : ℝ) ^ 2 / 1024) :
    ∃ D : ℕ, 0 < D ∧
      ∀ (State : Type v) (query : Ω → State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
        (update : Ω → State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
        (output : Ω → State → BlockSpace T (EuclideanSpace ℝ (Fin D))) (initial : Ω → State),
      (∀ f, Admissible p n Δ L f → Measurable (fun s =>
        ‖fderiv ℝ (average f) (componentJetOutput (query s) (update s) (output s) (initial s) N f)‖)) →
      ∃ f : Fin n → BlockSpace T (EuclideanSpace ℝ (Fin D)) → ℝ,
        Admissible p n Δ L f ∧ 1 / 4 ≤ P.real {s | ε <
          ‖fderiv ℝ (average f) (componentJetOutput (query s) (update s) (output s) (initial s) N f)‖} := by
  obtain ⟨D, hD, hdim, hfamily, htail⟩ := exists_chain_dimension T N q
  refine ⟨D, hD, ?_⟩
  intro State query update output initial hmeas
  have hρ : 0 < (m : ℝ) / n := by positivity
  let α := chainAlpha p L ((m : ℝ) / n) ε
  let β := chainBeta p L ((m : ℝ) / n) ε
  have hα := chainAlpha_pos p L ((m : ℝ) / n) ε hL hρ hε
  have hβ := chainBeta_pos p L ((m : ℝ) / n) ε hL hρ hε
  obtain ⟨f, hf, hfail⟩ := scaled_chain_fixed_failure P hn hD hm hmn hbalance hp
    query update output initial α β Δ L hα hβ N q
    (chain_parameters_gap p T Δ L _ ε hL hρ hε hT)
    (chain_parameters_smooth p (by omega) L _ ε hL hρ hε)
    hbudget hN hqueries hdim hfamily htail
    (fun f hf => measurableSet_lt (hmeas f hf) measurable_const)
  refine ⟨f, hf, hfail.trans (measureReal_mono ?_)⟩
  intro s hs
  have hab : α * β / 4 = 8 * ε := chainAlpha_beta p L _ ε hL hρ hε
  change α * β / 4 ≤ _ at hs
  rw [hab] at hs
  exact (show ε < 8 * ε by linarith).trans_le hs

end FullJet
