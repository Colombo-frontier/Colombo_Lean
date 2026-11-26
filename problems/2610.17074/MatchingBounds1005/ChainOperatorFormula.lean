import MatchingBounds1005.ChainCopies

/-! The coordinate action of the actual Riesz-represented chain Hessian. -/
noncomputable section
open scoped BigOperators InnerProductSpace

namespace MatchingBounds1005.BlockGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

def incomingHomogeneous {n : ℕ} (z : BlockSpace (E := E) n) (i : Fin (n + 1)) : ℝ :=
  ∑ j : Fin n, if j.succ = i then ⟪G.a, z j.castSucc⟫_ℝ else 0

theorem chainOperator_apply (n : ℕ) (z : BlockSpace (E := E) n) (i : Fin (n + 1)) :
    G.chainOperator n z i = G.H (z i) + (G.kappa * ⟪G.a, z i⟫_ℝ) • G.a -
      (G.lam * G.incomingHomogeneous z i) • G.e -
      (G.lam * G.outgoingEntry (fun j => z j) i) • G.a := by
  apply ext_inner_right ℝ
  intro v
  let w : BlockSpace (E := E) n := (WithLp.equiv 2 _).symm (Pi.single i v)
  have hi : ⟪G.chainOperator n z i, v⟫_ℝ = ⟪G.chainOperator n z, w⟫_ℝ := by
    change _ = ∑ j, ⟪G.chainOperator n z j, (Pi.single i v : Fin (n + 1) → E) j⟫_ℝ
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  have hH : (∑ j, ⟪z j, G.H (w j)⟫_ℝ) = ⟪G.H (z i), v⟫_ℝ := by
    rw [Finset.sum_eq_single i]
    · simp only [w, WithLp.equiv_symm_pi_apply, Pi.single_eq_same]
      exact G.symmetric _ _
    · intro j _ hji
      simp [w, Pi.single_eq_of_ne hji]
    · simp
  have ha : (∑ j, ⟪G.a, z j⟫_ℝ * ⟪G.a, w j⟫_ℝ) =
      ⟪G.a, z i⟫_ℝ * ⟪G.a, v⟫_ℝ := by
    rw [Finset.sum_eq_single i]
    · simp [w]
    · intro j _ hji
      simp [w, Pi.single_eq_of_ne hji]
    · simp
  have hin : (∑ j : Fin n, ⟪G.a, z j.castSucc⟫_ℝ * ⟪G.e, w j.succ⟫_ℝ) =
      G.incomingHomogeneous z i * ⟪G.e, v⟫_ℝ := by
    rw [incomingHomogeneous, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.succ = i
    · subst i
      simp [w]
    · simp [w, hj, Pi.single_eq_of_ne hj]
  have hout : (∑ j : Fin n, ⟪G.a, w j.castSucc⟫_ℝ * ⟪G.e, z j.succ⟫_ℝ) =
      G.outgoingEntry (fun j => z j) i * ⟪G.a, v⟫_ℝ := by
    rw [outgoingEntry, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.castSucc = i
    · subst i
      simp [w, mul_comm]
    · simp [w, hj, Pi.single_eq_of_ne hj]
  rw [hi, G.chainOperator_inner, G.chainBilinear_apply, hH, ha,
    Finset.sum_add_distrib, hin, hout]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
  ring

end MatchingBounds1005.BlockGeometry
