import NCConcave16991.DenseSmoothSigns
import NCConcave16991.DenseSmoothRevelationState
import NCConcave16991.DenseWeakRademacher

/-! # Public bounded probes and exact static-sign alignment scores -/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace NCConcave16991.DenseSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialProbe (x : E) : E := (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ • x

theorem radialProbe_norm_le (x : E) : ‖radialProbe x‖ ≤ 1 := by
  have hp : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hx : ‖x‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := by
    have hh := Real.sqrt_le_sqrt (by linarith [sq_nonneg ‖x‖] :
      ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ 2)
    simpa only [Real.sqrt_sq (norm_nonneg x)] using hh
  rw [radialProbe, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  simpa only [div_eq_mul_inv, mul_comm] using (div_le_one hp).mpr hx

theorem radialCoordinate_eq_probe (u x : E) :
    radialCoordinate u x = ⟪u, radialProbe x⟫_ℝ := by
  simp only [radialCoordinate, radialProbe, real_inner_smul_right, div_eq_mul_inv]
  ring

theorem euclidean_sum_squares_le {D : ℕ} (x : EuclideanSpace ℝ (Fin D))
    (hx : ‖x‖ ≤ 1) : (∑ d, x d ^ 2) ≤ 1 := by
  have hh : ∑ d, x d ^ 2 = ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [hh]
  nlinarith [norm_nonneg x]

theorem normalizedSignVector_inner {D : ℕ} (θ : Fin D → Fin 2)
    (v : EuclideanSpace ℝ (Fin D)) :
    ⟪normalizedSignVector (fun d ↦ DenseWeakHiding.hiddenSign (θ d)), v⟫_ℝ =
      (Real.sqrt (D : ℝ))⁻¹ * DenseWeakHiding.signedSum (fun d ↦ v d) θ := by
  rw [normalizedSignVector, real_inner_smul_left]
  congr 1
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ d, v d * DenseWeakHiding.hiddenSign (θ d)) =
    ∑ d, DenseWeakHiding.hiddenSign (θ d) * v d
  exact Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)

theorem coordinate_sign_score {n m D T : ℕ}
    (bank : Fin (T + 1) → Fin D → DenseWeakHiding.EncodedColumn n m)
    (x : Blocks (EuclideanSpace ℝ (Fin D)) T) (j : Fin (T + 1)) :
    coordinate (signDirection bank) x j =
      (Real.sqrt (D : ℝ))⁻¹ * DenseWeakHiding.signedSum
        (fun d ↦ radialProbe (x j) d) (fun d ↦ (bank j d).1) := by
  exact (radialCoordinate_eq_probe _ _).trans (normalizedSignVector_inner _ _)

theorem coordinate_alignment_score {n m D T : ℕ} (hD : 0 < D)
    (bank : Fin (T + 1) → Fin D → DenseWeakHiding.EncodedColumn n m)
    (x : Blocks (EuclideanSpace ℝ (Fin D)) T) (j : Fin (T + 1)) (a : ℝ)
    (ha : a ≤ coordinate (signDirection bank) x j) :
    a * Real.sqrt (D : ℝ) ≤ DenseWeakHiding.signedSum
      (fun d ↦ radialProbe (x j) d) (fun d ↦ (bank j d).1) := by
  have hp : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  rw [coordinate_sign_score] at ha
  have hh := mul_le_mul_of_nonneg_right ha hp.le
  calc
    _ ≤ ((Real.sqrt (D : ℝ))⁻¹ * DenseWeakHiding.signedSum
      (fun d ↦ radialProbe (x j) d) (fun d ↦ (bank j d).1)) * Real.sqrt (D : ℝ) := hh
    _ = _ := by field_simp

namespace Revelation

variable (E) [FiniteDimensional ℝ E] (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension E T) Ω)

def queryProbe (seed : Ω) (j : Fin (T + 1)) (s : State E n T hn ρ hρ) : E :=
  (action E n T hn ρ hρ P seed s).elim (fun _ ↦ 0)
    (fun o ↦ radialProbe (((primalCoordinates E T).symm o.2.1) j))

def finalProbe (seed : Ω) (j : Fin (T + 1)) (s : State E n T hn ρ hρ) : E :=
  radialProbe (((primalCoordinates E T).symm (output E n T hn ρ hρ P seed s)) j)

theorem queryProbe_norm_le (seed : Ω) (j : Fin (T + 1)) (s : State E n T hn ρ hρ) :
    ‖queryProbe E n T hn ρ hρ P seed j s‖ ≤ 1 := by
  unfold queryProbe
  cases action E n T hn ρ hρ P seed s with
  | inl x => simp
  | inr o => exact radialProbe_norm_le _

theorem finalProbe_norm_le (seed : Ω) (j : Fin (T + 1)) (s : State E n T hn ρ hρ) :
    ‖finalProbe E n T hn ρ hρ P seed j s‖ ≤ 1 := radialProbe_norm_le _

end Revelation
end NCConcave16991.DenseSmooth
