import MatchingBounds1005.Confinement
import MatchingBounds1005.SymmetricQuadratic
import MatchingBounds1005.SmoothClass

/-! Derivative assembly for the actual confined, masked, regularized objective. -/
noncomputable section
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.Confinement
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def regularizer (η : ℝ) (x : E) : ℝ := (η / 2) * ‖x‖ ^ 2

theorem regularizer_eq_energy (η : ℝ) :
    (regularizer η : E → ℝ) = SymmetricQuadratic.energy (η • ContinuousLinearMap.id ℝ E) 0 := by
  funext x
  simp only [regularizer, SymmetricQuadratic.energy, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_smul_right, real_inner_self_eq_norm_sq,
    ContinuousLinearMap.zero_apply, add_zero]
  ring

theorem scalar_id_symmetric (η : ℝ) (x y : E) :
    ⟪x, (η • ContinuousLinearMap.id ℝ E) y⟫_ℝ =
      ⟪(η • ContinuousLinearMap.id ℝ E) x, y⟫_ℝ := by
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left, inner_smul_right]

theorem regularizer_smooth (η : ℝ) : ContDiff ℝ ∞ (regularizer η : E → ℝ) := by
  rw [regularizer_eq_energy]
  exact SymmetricQuadratic.smooth _ _

theorem regularizer_jet_bound (η : ℝ) (j : ℕ) (hj : 2 ≤ j) (x : E) :
    ‖iteratedFDeriv ℝ j (regularizer η) x‖ ≤ if j = 2 then |η| else 0 := by
  rw [regularizer_eq_energy]
  by_cases hj2 : j = 2
  · subst j
    rw [if_pos rfl]
    apply (SymmetricQuadratic.second_bound _ _ (scalar_id_symmetric η) x).trans
    apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg η)
    intro y
    change ‖η • y‖ ≤ |η| * ‖y‖
    simp only [norm_smul, Real.norm_eq_abs, le_rfl]
  · rw [if_neg hj2]
    have hj3 : j = (j - 3) + 3 := by omega
    rw [hj3, SymmetricQuadratic.higher_zero _ _ (scalar_id_symmetric η),
      Pi.zero_apply, norm_zero]

theorem objective_eq_add (V : E → ℝ) (R η : ℝ) :
    objective V R η = (V ∘ radial R) + regularizer η := rfl

theorem objective_smooth {V : E → ℝ} (hV : ContDiff ℝ ∞ V) (R η : ℝ) :
    ContDiff ℝ ∞ (objective V R η) := by
  rw [objective_eq_add]
  exact (hV.comp (radial_contDiff R ∞)).add (regularizer_smooth η)

theorem objective_jet_bound {V : E → ℝ} (hV : ContDiff ℝ ∞ V) (R η : ℝ)
    (j : ℕ) (hj : 2 ≤ j) (x : E) :
    ‖iteratedFDeriv ℝ j (objective V R η) x‖ ≤
      ‖iteratedFDeriv ℝ j (V ∘ radial R) x‖ + if j = 2 then |η| else 0 := by
  have hlevel : (j : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  rw [objective_eq_add, iteratedFDeriv_add_apply
    ((hV.comp (radial_contDiff R ∞)).of_le hlevel).contDiffAt
    ((regularizer_smooth η).of_le hlevel).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add_left (regularizer_jet_bound η j hj x) _)

theorem masked_objective_jet_bound {F P : E → ℝ}
    (hF : ContDiff ℝ ∞ F) (hP : ContDiff ℝ ∞ P) (R η : ℝ)
    (j : ℕ) (hj : 2 ≤ j) (x : E) :
    ‖iteratedFDeriv ℝ j (objective (fun y => F y + P y) R η) x‖ ≤
      ‖iteratedFDeriv ℝ j (F ∘ radial R) x‖ +
        ‖iteratedFDeriv ℝ j (P ∘ radial R) x‖ + if j = 2 then |η| else 0 := by
  have hlevel : (j : WithTop ℕ∞) ≤ ∞ :=
    by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  have h := objective_jet_bound (hF.add hP) R η j hj x
  have heq : (fun y => F y + P y) ∘ radial R = (F ∘ radial R) + (P ∘ radial R) := rfl
  rw [heq, iteratedFDeriv_add_apply
    ((hF.comp (radial_contDiff R ∞)).of_le hlevel).contDiffAt
    ((hP.comp (radial_contDiff R ∞)).of_le hlevel).contDiffAt] at h
  exact h.trans (add_le_add_right (norm_add_le _ _) _)

end MatchingBounds1005.Confinement

namespace MatchingBounds1005.Model

theorem confined_inFunctionClass {d p : ℕ} {F P : Space d → ℝ}
    (hF : ContDiff ℝ ∞ F) (hP : ContDiff ℝ ∞ P) (R η : ℝ)
    (B M : ℕ → ℝ)
    (hbase : ∀ q, 1 ≤ q → q ≤ p → ∀ x : Space d,
      ‖iteratedFDeriv ℝ (q + 1) (F ∘ radial R) x‖ ≤ B q)
    (hmask : ∀ q, 1 ≤ q → q ≤ p → ∀ x : Space d,
      ‖iteratedFDeriv ℝ (q + 1) (P ∘ radial R) x‖ ≤ M q)
    (hbudget : ∀ q, 1 ≤ q → q ≤ p → B q + M q + (if q = 1 then |η| else 0) ≤ 1)
    (hgap : ∀ x, Confinement.objective (fun y => F y + P y) R η 0 -
      Confinement.objective (fun y => F y + P y) R η x ≤ 1) :
    InFunctionClass p (Confinement.objective (fun y => F y + P y) R η) := by
  apply inFunctionClass_of_operator_bounds (Confinement.objective_smooth (hF.add hP) R η) hgap
  intro q hq hqp x
  have h := Confinement.masked_objective_jet_bound hF hP R η (q + 1) (by omega) x
  have heq : (q + 1 = 2) ↔ q = 1 := by omega
  simp only [heq] at h
  exact h.trans ((add_le_add_right (add_le_add (hbase q hq hqp x) (hmask q hq hqp x)) _).trans
    (hbudget q hq hqp))

end MatchingBounds1005.Model
