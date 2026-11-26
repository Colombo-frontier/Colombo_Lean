import NCConcave16991.BranchOracleCorrelation
import NCConcave16991.BranchOracleFamily
import NCConcave16991.BranchOracleRelease
import NCConcave16991.BranchOracleGlobal

/-! # The actual common reservoir event makes every unreleased source flat -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard LocalizationScalar LocalizationRadial
open scoped InnerProductSpace

def flatThreshold : ℝ := deltaGate / 20
def releaseThreshold : ℝ := flatThreshold ^ 2 / 2

theorem flatThreshold_pos : 0 < flatThreshold := div_pos deltaGate_pos (by norm_num)
theorem releaseThreshold_pos : 0 < releaseThreshold := div_pos (sq_pos_of_pos flatThreshold_pos) (by norm_num)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def markedState (s : E) : E := (1 / 20 : ℝ) • radialCap 10 s

theorem markedState_norm_le (s : E) : ‖markedState s‖ ≤ 1 := by
  have hb := (radialCap_value_bounds (by norm_num : (0 : ℝ) < 10) s).trans (min_le_right _ _)
  simp only [markedState, norm_smul, Real.norm_eq_abs]
  norm_num at hb ⊢
  linarith

theorem stateScore_eq_marked (v s : E) : stateScore v s = 20 * ⟪v, markedState s⟫_ℝ := by
  simp only [stateScore, markedState, real_inner_smul_right]
  ring

theorem markedState_inverse_mem {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (Q : E ≃ₗᵢ[ℝ] F) (S : Submodule ℝ E) (s : F) (hs : Q.symm s ∈ S) :
    Q.symm (markedState s) ∈ S := by
  let K : Submodule ℝ F := S.comap Q.symm.toLinearMap
  have hle : Submodule.span ℝ ({s} : Set F) ≤ K := by
    apply Submodule.span_le.mpr
    intro x hx
    have he : x = s := by simpa only [Set.mem_singleton_iff] using hx
    subst x
    exact hs
  exact K.smul_mem (1 / 20 : ℝ) (hle (radialCap_mem_span 10 s))

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- This is a consequence of actual support and the true reservoir projection,
including completely unrestricted norms of the original physical state. -/
theorem stateScore_flat_of_support {t : ℕ} (p : WordProfile ι) (W : Submodule ℝ E)
    [W.HasOrthogonalProjection] (e : E) (he : ‖e‖ = 1)
    (Q : FormalLayer (ι := ι) E t ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E t)
    (s : FormalLayer (ι := ι) E t) (hs : Q.symm s ∈ wordSupport t (p.words t) W)
    (hmass : p.mass t < releaseThreshold) (hreservoir : ‖W.orthogonalProjectionOnto e‖ ^ 2 ≤ releaseThreshold) :
    |stateScore (Q (formalTarget E t e)) s| < deltaGate := by
  have hm := markedState_inverse_mem Q (wordSupport t (p.words t) W) s hs
  have hc := rotated_wordSupport_correlation (p.words t) W e he Q (markedState s) hm (markedState_norm_le s)
  have hc' : ⟪Q (formalTarget E t e), markedState s⟫_ℝ ^ 2 < flatThreshold ^ 2 := by
    change _ ≤ p.mass t + ‖W.starProjection e‖ ^ 2 at hc
    change ‖W.starProjection e‖ ^ 2 ≤ releaseThreshold at hreservoir
    dsimp [releaseThreshold] at hmass hreservoir
    linarith
  have ha : |⟪Q (formalTarget E t e), markedState s⟫_ℝ| < flatThreshold := by
    apply (sq_lt_sq₀ (abs_nonneg _) flatThreshold_pos.le).mp
    simpa only [sq_abs] using hc'
  rw [stateScore_eq_marked, abs_mul]
  norm_num
  dsimp [flatThreshold] at ha
  linarith

def macroSite (m : ℕ) {M : ℕ} (j : Fin M) : ℕ := j.val * (m + 1) + (m + 1)

theorem macroSite_strictMono (m M : ℕ) : StrictMono (macroSite m : Fin M → ℕ) := by
  intro i j hij
  dsimp [macroSite]
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hij (show 0 < m + 1 by omega)) (m + 1)

theorem macro_inactive_scores_of_closed {M m : ℕ}
    (Q : ∀ d : ℕ, FormalLayer (ι := ι) E d ≃ₗᵢ[ℝ] FormalLayer (ι := ι) E d)
    (e : E) (he : ‖e‖ = 1) (p : WordProfile ι) (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (r : ℕ) (z : GlobalHard.Joint (MacroSpaces (ι := ι) E M m))
    (hclosed : WordProfile.ReleaseClosed releaseThreshold (macroSite (M := M) m) r p)
    (hsupport : ∀ j : Fin M, (Q (macroSite m j)).symm (stateProj (MacroSpaces (ι := ι) E M m) j z) ∈
      wordSupport (macroSite m j) (p.words (macroSite m j)) W)
    (hreservoir : ‖W.orthogonalProjectionOnto e‖ ^ 2 ≤ releaseThreshold) :
    ∀ j : Fin M, r ≤ j.val →
      |score (MacroSpaces (ι := ι) E M m) (terminalSources E Q e) j z| < deltaGate := by
  intro j hj
  exact stateScore_flat_of_support p W e he (Q (macroSite m j))
    (stateProj (MacroSpaces (ι := ι) E M m) j z) (hsupport j) (hclosed j hj) hreservoir

end
end NCConcave16991.BranchOracle
