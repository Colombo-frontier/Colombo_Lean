import HeavyTail.OracleModel

/-! A common public quadratic block for all lower-bound families. The public
proximal contract is proved for the explicit map; no private objective appears. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace
namespace HeavyTail

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem quadraticRegularizer_strongConvex (μ : ℝ) :
    StrongConvexOn (Set.univ : Set E) μ (fun x => μ / 2 * ‖x‖ ^ 2) := by
  rw [strongConvexOn_iff_convex]
  simpa only [sub_self] using (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))

theorem quadraticProx_objective_identity {μ η : ℝ} (hμ : 0 ≤ μ) (hη : 0 < η) (z y : E) :
    (μ / 2 * ‖y‖ ^ 2 + ‖y - z‖ ^ 2 / (2 * η)) -
      (μ / 2 * ‖(1 + η * μ)⁻¹ • z‖ ^ 2 +
        ‖(1 + η * μ)⁻¹ • z - z‖ ^ 2 / (2 * η)) =
      (μ + η⁻¹) / 2 * ‖y - (1 + η * μ)⁻¹ • z‖ ^ 2 := by
  have hd : 1 + η * μ ≠ 0 := ne_of_gt (by positivity)
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp [hd, hη.ne']
  <;> ring

def quadraticProximalOracle (μ : ℝ) (hμ : 0 ≤ μ) :
    ProximalOracle (Set.univ : Set E) (fun x => μ / 2 * ‖x‖ ^ 2) where
  point η z := (1 + η * μ)⁻¹ • z
  feasible _ _ _ := Set.mem_univ _
  minimizing η hη z y _ := by
    have he := quadraticProx_objective_identity E hμ hη z y
    have hn : 0 ≤ (μ + η⁻¹) / 2 * ‖y - (1 + η * μ)⁻¹ • z‖ ^ 2 := by positivity
    linarith only [he, hn]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def quadraticPublicProblem (θ : OracleParameters) : PublicProblem E θ where
  X := Set.univ
  X_nonempty := ⟨0, Set.mem_univ _⟩
  X_closed := isClosed_univ
  X_convex := convex_univ
  S := Set.univ
  domain_nonempty := ⟨0, Set.mem_univ _⟩
  domain_subset := Set.Subset.rfl
  h x := θ.μ / 2 * ‖x‖ ^ 2
  epigraph_closed := by
    have hc : Continuous (fun z : E × ℝ => θ.μ / 2 * ‖z.1‖ ^ 2) :=
      continuous_const.mul (continuous_fst.norm.pow 2)
    simpa only [Set.mem_univ, true_and] using isClosed_le hc continuous_snd
  h_convex := strongConvexOn_zero.mp
    (StrongConvexOn.mono θ.μ_nonneg (quadraticRegularizer_strongConvex E θ.μ))
  h_strongConvex := quadraticRegularizer_strongConvex E θ.μ
  prox := quadraticProximalOracle E θ.μ θ.μ_nonneg
  initial := 0
  initial_feasible := Set.mem_univ _

@[simp] theorem quadraticPublicProblem_X (θ : OracleParameters) :
    (quadraticPublicProblem E θ).X = Set.univ := rfl

@[simp] theorem quadraticPublicProblem_S (θ : OracleParameters) :
    (quadraticPublicProblem E θ).S = Set.univ := rfl

@[simp] theorem quadraticPublicProblem_h (θ : OracleParameters) (x : E) :
    (quadraticPublicProblem E θ).h x = θ.μ / 2 * ‖x‖ ^ 2 := rfl

@[simp] theorem quadraticPublicProblem_initial (θ : OracleParameters) :
    (quadraticPublicProblem E θ).initial = 0 := rfl

end HeavyTail
