import FullJet.Simulation
import FullJet.ChainOpacity

namespace FullJet

/-- Before the reference run hits a designated event, the two actual states
agree. The oracle agreement is needed only away from that event. -/
theorem oracleRun_eq_before_hit {State Query Reply : Type*}
    (query : State → Query) (update : State → Reply → State)
    (oracle reference : Query → Reply) (initial : State) (hit : State → Prop)
    (hagree : ∀ s, ¬ hit s → oracle (query s) = reference (query s))
    (q : ℕ) (hbefore : ∀ t < q, ¬ hit (oracleRun query update reference initial t)) :
    oracleRun query update oracle initial q = oracleRun query update reference initial q := by
  apply oracleRun_eq_of_agree
  intro t ht
  exact hagree _ (hbefore t ht)

/-- An actual hit by time `q` also occurs on the reference path. This includes
the final output state at `q`, not just the states before oracle calls. -/
theorem oracleRun_hit_transfer {State Query Reply : Type*}
    (query : State → Query) (update : State → Reply → State)
    (oracle reference : Query → Reply) (initial : State) (hit : State → Prop)
    (hagree : ∀ s, ¬ hit s → oracle (query s) = reference (query s)) (q : ℕ)
    (hactual : ∃ t ≤ q, hit (oracleRun query update oracle initial t)) :
    ∃ t ≤ q, hit (oracleRun query update reference initial t) := by
  by_contra h
  push_neg at h
  obtain ⟨t, ht, hhit⟩ := hactual
  have heq := oracleRun_eq_before_hit query update oracle reference initial hit hagree t
    (fun s hs => h s (by omega))
  rw [heq] at hhit
  exact h t ht hhit

theorem oracleRun_hit_iff {State Query Reply : Type*}
    (query : State → Query) (update : State → Reply → State)
    (oracle reference : Query → Reply) (initial : State) (hit : State → Prop)
    (hagree : ∀ s, ¬ hit s → oracle (query s) = reference (query s)) (q : ℕ) :
    (∃ t ≤ q, hit (oracleRun query update oracle initial t)) ↔
      ∃ t ≤ q, hit (oracleRun query update reference initial t) := by
  constructor
  · exact oracleRun_hit_transfer query update oracle reference initial hit hagree q
  · exact oracleRun_hit_transfer query update reference oracle initial hit (fun s hs => (hagree s hs).symm) q

abbrev JetPacket (p : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (r : Fin (p + 1)) → E [×r.val]→L[ℝ] ℝ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T n p : ℕ}

noncomputable def chainOracle (θ : Fin (T + 1) → E) (s : Fin n → Fin (T + 1) → E)
    (ρ lam : ℝ) (p : ℕ) (z : Fin n × BlockSpace T E) : JetPacket p (BlockSpace T E) :=
  fullJet p (componentChain θ (s z.1) ρ lam) z.2

noncomputable def truncatedChainOracle (θ : Fin (T + 1) → E) (s : Fin n → Fin (T + 1) → E)
    (ρ lam : ℝ) (p : ℕ) (retained : Finset (Fin T))
    (z : Fin n × BlockSpace T E) : JetPacket p (BlockSpace T E) :=
  fullJet p (truncatedComponentChain θ (s z.1) ρ lam retained) z.2

/-- The concrete full-jet and truncated-chain runs coincide until a removed
gate is crossed. This instantiates the coupling with proved jet opacity. -/
theorem chainOracleRun_eq_before_open {State : Type*}
    (query : State → Fin n × BlockSpace T E) (update : State → JetPacket p (BlockSpace T E) → State)
    (θ : Fin (T + 1) → E) (s : Fin n → Fin (T + 1) → E) (ρ lam : ℝ)
    (retained : Finset (Fin T)) (initial : State) (q : ℕ)
    (hclosed : ∀ t < q, ∀ j ∉ retained, alignment (θ j.castSucc)
      ((query (oracleRun query update (truncatedChainOracle θ s ρ lam p retained) initial t)).2 j.castSucc) ≤ 5 / 32) :
    oracleRun query update (chainOracle θ s ρ lam p) initial q =
      oracleRun query update (truncatedChainOracle θ s ρ lam p retained) initial q := by
  apply oracleRun_eq_of_agree
  intro t ht
  exact componentChain_fullJet_eq_truncated θ _ ρ lam retained _ (hclosed t ht) p

theorem chainOracleRun_open_iff {State : Type*}
    (query : State → Fin n × BlockSpace T E) (update : State → JetPacket p (BlockSpace T E) → State)
    (θ : Fin (T + 1) → E) (s : Fin n → Fin (T + 1) → E) (ρ lam : ℝ)
    (retained : Finset (Fin T)) (initial : State) (q : ℕ) :
    (∃ t ≤ q, ∃ j ∉ retained, 5 / 32 < alignment (θ j.castSucc)
      ((query (oracleRun query update (chainOracle θ s ρ lam p) initial t)).2 j.castSucc)) ↔
    (∃ t ≤ q, ∃ j ∉ retained, 5 / 32 < alignment (θ j.castSucc)
      ((query (oracleRun query update (truncatedChainOracle θ s ρ lam p retained) initial t)).2 j.castSucc)) := by
  apply oracleRun_hit_iff query update (chainOracle θ s ρ lam p)
    (truncatedChainOracle θ s ρ lam p retained) initial
    (fun state => ∃ j ∉ retained, 5 / 32 < alignment (θ j.castSucc) ((query state).2 j.castSucc))
  intro state h
  push_neg at h
  exact componentChain_fullJet_eq_truncated θ _ ρ lam retained _ h p

end FullJet
