import FullJet.RescaledOracle

open MeasureTheory

namespace FullJet

noncomputable def sampledScaledComponents {n D k T : ℕ}
    (x : Fin (T + 1) → FixedTableSample n D k) (ρ α β : ℝ) :
    Fin n → BlockSpace T (EuclideanSpace ℝ (Fin D)) → ℝ :=
  fun i => scaledComponentChain (fun j => sampledDirection (x j))
    (fun j => sampledRow (x j) i) ρ (33 / 16) α β

theorem sampledScaledComponents_average {n D k m T : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hbalance : 2 * k = n + m) (x : Fin (T + 1) → FixedTableSample n D k) (α β : ℝ) :
    average (sampledScaledComponents x ((m : ℝ) / n) α β) =
      fun z => α * baseChain (fun j => sampledDirection (x j)) (33 / 16) (β • z) := by
  funext z
  change average (fun i y => α * componentChain (fun j => sampledDirection (x j))
    (fun j => sampledRow (x j) i) ((m : ℝ) / n) (33 / 16) (β • y)) z = _
  rw [average_rescale]
  congr 1
  exact componentChain_average hn _ _ _ _ (by positivity)
    (fun j => sampledRow_table_average hn hbalance (x j)) _

theorem sampledScaledComponents_gradient_norm {n D k m T : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hbalance : 2 * k = n + m) (x : Fin (T + 1) → FixedTableSample n D k)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (z : BlockSpace T (EuclideanSpace ℝ (Fin D))) :
    ‖fderiv ℝ (average (sampledScaledComponents x ((m : ℝ) / n) α β)) z‖ =
      α * β * ‖fderiv ℝ (baseChain (fun j => sampledDirection (x j)) (33 / 16)) (β • z)‖ := by
  rw [sampledScaledComponents_average hn hm hbalance]
  apply norm_fderiv_rescale _ α β hα hβ z
  rw [baseChain_eq_componentChain]
  exact (componentChain_contDiff _ _ _ _).differentiable (by simp)

theorem sampledScaledComponents_output {State : Type*} {n D k T p : ℕ}
    (query : State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : State → BlockSpace T (EuclideanSpace ℝ (Fin D))) (initial : State)
    (x : Fin (T + 1) → FixedTableSample n D k) (ρ α β : ℝ) (N : ℕ) :
    β • componentJetOutput query update output initial N (sampledScaledComponents x ρ α β) =
      β • output (oracleRun (rescaleQuery β query) (rescaleUpdate α β update)
        (sampledChainOracle x ρ (33 / 16) p) initial N) := by
  exact componentJetOutput_rescale query update output initial _
    (fun _ => componentChain_contDiff _ _ _ _) α β N

def scaledChainSeedSuccess {Ω State : Type*} {n D k T p : ℕ}
    (query : Ω → State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : Ω → State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : Ω → State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : Ω → State) (ρ α β : ℝ) (N : ℕ) (x : Fin (T + 1) → FixedTableSample n D k) : Set Ω :=
  {s | ‖fderiv ℝ (average (sampledScaledComponents x ρ α β))
    (componentJetOutput (query s) (update s) (output s) (initial s) N
      (sampledScaledComponents x ρ α β))‖ < α * β / 4}

/-- The probability event is transported exactly, not merely the norm bound
at a prescribed point. Queries, internal state and output are all simulated. -/
theorem scaledChainSeedSuccess_eq {Ω State : Type*} {n D k m T p : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hbalance : 2 * k = n + m)
    (query : Ω → State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : Ω → State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : Ω → State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : Ω → State) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (N : ℕ)
    (x : Fin (T + 1) → FixedTableSample n D k) :
    scaledChainSeedSuccess query update output initial ((m : ℝ) / n) α β N x =
      chainSeedSuccess (fun s => rescaleQuery β (query s)) (fun s => rescaleUpdate α β (update s))
        (fun s state => β • output s state) initial ((m : ℝ) / n) N x := by
  ext s
  change ‖fderiv ℝ (average (sampledScaledComponents x ((m : ℝ) / n) α β)) _‖ < α * β / 4 ↔ _
  rw [sampledScaledComponents_gradient_norm hn hm hbalance x α β hα.le hβ.le,
    sampledScaledComponents_output]
  change α * β * _ < α * β / 4 ↔ _
  rw [show α * β / 4 = α * β * (1 / 4) by ring, mul_lt_mul_left (mul_pos hα hβ)]
  rfl

/-- The complete randomized lower bound on actual scaled component jets.
Every returned sample satisfies the requested class constraints. -/
theorem scaled_chain_fixed_failure {Ω State : Type*} [MeasurableSpace Ω] {n D k m T p : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (hn : 0 < n) (hD : 0 < D)
    (hm : 0 < m) (hmn : m ≤ n) (hbalance : 2 * k = n + m) (hp : 2 ≤ p)
    (query : Ω → State → Fin n × BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (update : Ω → State → JetPacket p (BlockSpace T (EuclideanSpace ℝ (Fin D))) → State)
    (output : Ω → State → BlockSpace T (EuclideanSpace ℝ (Fin D)))
    (initial : Ω → State) (α β Δ L : ℝ) (hα : 0 < α) (hβ : 0 < β) (N q : ℕ)
    (hgap : α * (2 * (T + 1 : ℕ)) ≤ Δ)
    (hsmooth : α * β ^ (p + 1) * (chainDerivativeBound (p + 1) / ((m : ℝ) / n)) ≤ L)
    (hbudget : 8 * (m : ℝ) + 9 * (q + 1 : ℕ) ≤ n) (hN : 2 * N ≤ (q + 1) * (T + 1))
    (hqueries : (q + 1 : ℕ) * ((m : ℝ) / n) ^ 2 ≤ (5 / 32 : ℝ) ^ 2 / 1024)
    (hdim : 32 * Real.log 2 ≤ (5 / 32 : ℝ) ^ 2 * D)
    (hfamily : (2 : ℝ) * (q + 1 : ℕ) ≤ Real.exp ((5 / 32 : ℝ) ^ 2 * D / 4))
    (htail : 2 * (T + 1 : ℕ) ^ 2 * (N + 1 : ℕ) * Real.exp (-((5 / 32 : ℝ) ^ 2 * D / 2)) ≤ 1 / 4)
    (hmeas : ∀ f, Admissible p n Δ L f → MeasurableSet {s |
      ‖fderiv ℝ (average f) (componentJetOutput (query s) (update s) (output s) (initial s) N f)‖ < α * β / 4}) :
    ∃ f : Fin n → BlockSpace T (EuclideanSpace ℝ (Fin D)) → ℝ,
      Admissible p n Δ L f ∧ 1 / 4 ≤ P.real {s | α * β / 4 ≤
        ‖fderiv ℝ (average f) (componentJetOutput (query s) (update s) (output s) (initial s) N f)‖} := by
  have hk : k ≤ n := by omega
  have hadm (x : Fin (T + 1) → FixedTableSample n D k) :
      Admissible p n Δ L (sampledScaledComponents x ((m : ℝ) / n) α β) :=
    sampledChain_admissible hn hD hm hmn hbalance hp x α β Δ L hα.le hβ.le hgap hsmooth
  have heq := scaledChainSeedSuccess_eq hn hm hbalance query update output initial α β hα hβ N
  obtain ⟨x, hx⟩ := randomized_chain_fixed_failure P hn hD hk (m : ℝ) (by positivity)
    (by exact_mod_cast hbalance) (fun s => rescaleQuery β (query s))
    (fun s => rescaleUpdate α β (update s)) (fun s state => β • output s state) initial
    ((m : ℝ) / n) N q hbudget hN hqueries hdim hfamily htail (fun x => by
      rw [← heq x]
      exact hmeas _ (hadm x))
  rw [← heq x] at hx
  refine ⟨sampledScaledComponents x ((m : ℝ) / n) α β, hadm x, ?_⟩
  simpa only [scaledChainSeedSuccess, Set.compl_setOf, not_lt] using hx

end FullJet
