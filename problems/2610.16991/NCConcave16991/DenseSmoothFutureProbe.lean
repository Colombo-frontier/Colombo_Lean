import NCConcave16991.DenseSmoothProbeAlignment
import NCConcave16991.DenseSmoothRevelationPrefix
import NCConcave16991.DenseSmoothRevelationCoupling

/-! # Bounded future-stage probes depend on strict-past tables only -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open scoped InnerProductSpace

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension E T) Ω)

def futureProbe (seed : Ω) (A : Table E n T ρ) (N t : ℕ) (j : Fin (T + 1)) : E :=
  (prefixView E n T hn ρ hρ j (runWithTable E n T hn ρ hρ P seed A t)).elim 0
    (fun s ↦ if t < N then queryProbe E n T hn ρ hρ P seed j s
      else finalProbe E n T hn ρ hρ P seed j s)

theorem futureProbe_norm_le (seed : Ω) (A : Table E n T ρ) (N t : ℕ) (j : Fin (T + 1)) :
    ‖futureProbe E n T hn ρ hρ P seed A N t j‖ ≤ 1 := by
  unfold futureProbe
  cases prefixView E n T hn ρ hρ j (runWithTable E n T hn ρ hρ P seed A t) with
  | none => simp
  | some s =>
      simp only [Option.elim_some]
      split_ifs
      · exact queryProbe_norm_le E n T hn ρ hρ P seed j s
      · exact finalProbe_norm_le E n T hn ρ hρ P seed j s

theorem futureProbe_eq_of_prefix (seed : Ω) (A B : Table E n T ρ)
    (j : Fin (T + 1)) (hAB : SamePrefix E n T ρ j A B) (N t : ℕ) :
    futureProbe E n T hn ρ hρ P seed A N t j = futureProbe E n T hn ρ hρ P seed B N t j := by
  unfold futureProbe
  rw [run_prefix_eq E n T hn ρ hρ P seed j A B hAB t]

theorem futureProbe_query (seed : Ω) (A : Table E n T ρ) (N t : ℕ) (j : Fin (T + 1))
    (ht : t < N) (hj : frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t) < j.val)
    (o : Query E n T hn ρ hρ)
    (ho : action E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed A t) = .inr o) :
    futureProbe E n T hn ρ hρ P seed A N t j =
      radialProbe (((primalCoordinates E T).symm o.2.1) j) := by
  simp only [futureProbe,prefixView,hj,ite_true,Option.elim_some,ht]
  exact queryProbe_eq E n T hn ρ hρ P seed j _ o ho

theorem futureProbe_final (seed : Ω) (A : Table E n T ρ) (N : ℕ) (j : Fin (T + 1))
    (hj : frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A N) < j.val) :
    futureProbe E n T hn ρ hρ P seed A N N j =
      radialProbe (((primalCoordinates E T).symm
        (output E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed A N))) j) := by
  simp only [futureProbe,prefixView,hj,ite_true,Option.elim_some,lt_self_iff_false,ite_false,finalProbe]

def NoFutureAlignment (seed : Ω) (A : Table E n T ρ) (N : ℕ) : Prop :=
  ∀ t ≤ N, ∀ j : Fin (T + 1),
    ⟪A.direction j,futureProbe E n T hn ρ hρ P seed A N t j⟫_ℝ ≤ (5 / 32 : ℝ)

theorem noFutureAlignment_queryGood (seed : Ω) (A : Table E n T ρ) (N : ℕ)
    (h : NoFutureAlignment E n T hn ρ hρ P seed A N) :
    FutureGoodBefore E n T hn ρ hρ P seed A N := by
  intro t ht o ho j hj
  have hh := h t ht.le j.castSucc
  rw [futureProbe_query E n T hn ρ hρ P seed A N t j.castSucc ht hj o ho] at hh
  simpa only [coordinate,radialCoordinate_eq_probe] using hh

theorem noFutureAlignment_outputGood (seed : Ω) (A : Table E n T ρ) (N : ℕ)
    (h : NoFutureAlignment E n T hn ρ hρ P seed A N) :
    ∀ j : Fin (T + 1), frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A N) < j.val →
      coordinate A.direction ((primalCoordinates E T).symm
        (output E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed A N))) j ≤ (5 / 32 : ℝ) := by
  intro j hj
  have hh := h N le_rfl j
  rw [futureProbe_final E n T hn ρ hρ P seed A N j hj] at hh
  simpa only [coordinate,radialCoordinate_eq_probe] using hh

end
end NCConcave16991.DenseSmooth.Revelation
