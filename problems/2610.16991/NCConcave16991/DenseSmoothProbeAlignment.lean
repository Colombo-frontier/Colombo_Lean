import NCConcave16991.DenseSmoothProbe

/-! # Actual completion tests give the public signed-sum probe event -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open scoped InnerProductSpace

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension E T) Ω)

theorem queryProbe_eq (seed : Ω) (j : Fin (T + 1)) (s : State E n T hn ρ hρ)
    (o : Query E n T hn ρ hρ) (ho : action E n T hn ρ hρ P seed s = .inr o) :
    queryProbe E n T hn ρ hρ P seed j s =
      radialProbe (((primalCoordinates E T).symm o.2.1) j) := by
  simp only [queryProbe,ho,Sum.elim_inr]

theorem completion_query_alignment (seed : Ω) (A : Table E n T ρ)
    (s : State E n T hn ρ hρ)
    (hc : completion E n T hn ρ hρ P seed A s = true) :
    (5 / 32 : ℝ) < ⟪A.direction (stageIndex E n T hn ρ hρ s),
      queryProbe E n T hn ρ hρ P seed (stageIndex E n T hn ρ hρ s) s⟫_ℝ := by
  unfold completion at hc
  cases ha : action E n T hn ρ hρ P seed s with
  | inl x => simp only [ha,Sum.elim_inl,Bool.false_eq_true] at hc
  | inr o =>
      have hq : (5 / 32 : ℝ) < coordinate A.direction ((primalCoordinates E T).symm o.2.1)
          (stageIndex E n T hn ρ hρ s) := by
        by_cases hf : frontier E n T hn ρ hρ s < T + 1
        · simpa only [ha,Sum.elim_inr,hf,ite_true,decide_eq_true_eq] using hc
        · simp only [ha,Sum.elim_inr,hf,ite_false,Bool.false_eq_true] at hc
      rw [queryProbe_eq E n T hn ρ hρ P seed _ s o ha]
      simpa only [coordinate,radialCoordinate_eq_probe] using hq

variable (D : ℕ)
  (Q : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension (EuclideanSpace ℝ (Fin D)) T) Ω)

theorem queryProbe_sum_squares (seed : Ω) (j : Fin (T + 1))
    (s : State (EuclideanSpace ℝ (Fin D)) n T hn ρ hρ) :
    (∑ d, queryProbe (EuclideanSpace ℝ (Fin D)) n T hn ρ hρ Q seed j s d ^ 2) ≤ 1 :=
  euclidean_sum_squares_le _ (queryProbe_norm_le _ _ _ _ _ _ _ _ _ _)

theorem finalProbe_sum_squares (seed : Ω) (j : Fin (T + 1))
    (s : State (EuclideanSpace ℝ (Fin D)) n T hn ρ hρ) :
    (∑ d, finalProbe (EuclideanSpace ℝ (Fin D)) n T hn ρ hρ Q seed j s d ^ 2) ≤ 1 :=
  euclidean_sum_squares_le _ (finalProbe_norm_le _ _ _ _ _ _ _ _ _ _)

theorem completion_signedSum {m : ℕ} (hD : 0 < D) (seed : Ω)
    (bank : Fin (T + 1) → Fin D → DenseWeakHiding.EncodedColumn n m)
    (s : State (EuclideanSpace ℝ (Fin D)) n T hn ρ hρ)
    (A : Table (EuclideanSpace ℝ (Fin D)) n T ρ)
    (hA : A.direction = signDirection bank)
    (hc : completion (EuclideanSpace ℝ (Fin D)) n T hn ρ hρ Q seed A s = true) :
    (5 / 32 : ℝ) * Real.sqrt (D : ℝ) ≤ DenseWeakHiding.signedSum
      (fun d ↦ queryProbe (EuclideanSpace ℝ (Fin D)) n T hn ρ hρ Q seed
        (stageIndex (EuclideanSpace ℝ (Fin D)) n T hn ρ hρ s) s d)
      (fun d ↦ (bank (stageIndex (EuclideanSpace ℝ (Fin D)) n T hn ρ hρ s) d).1) := by
  have hp : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have hh := completion_query_alignment _ _ _ _ _ _ Q seed A s hc
  rw [hA,signDirection,normalizedSignVector_inner] at hh
  have he := mul_lt_mul_of_pos_right hh hp
  apply le_of_lt
  convert he using 1 <;> field_simp

end
end NCConcave16991.DenseSmooth.Revelation
