import NCBall.NoiseEmbedding
import NCBall.ShadowValue
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The transverse Gaussian coordinates used by an actual room query -/

noncomputable section
open scoped InnerProductSpace
namespace NCBall

abbrev Transverse (n : ℕ) := EuclideanSpace ℝ (Fin n)

def transverseEmbed (n : ℕ) : Transverse n →ₗᵢ[ℝ] Space n where
  toFun x := transverseVector (fun i => x i)
  map_add' := by
    intro x y
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [transverseVector]
    · rfl
  map_smul' := by
    intro a x
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [transverseVector]
    · rfl
  norm_map' := by
    intro x
    change ‖transverseVector (fun i => x i)‖ = ‖x‖
    have he := transverseVector_norm_sq (fun i => x i)
    have hx : ‖x‖ ^ 2 = coordinateNormSq (fun i => x i) := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp [coordinateNormSq, Real.norm_eq_abs, sq_abs]
    nlinarith [norm_nonneg x, norm_nonneg (transverseVector (fun i => x i))]

def transverseProjection (n : ℕ) : Space n →L[ℝ] Transverse n :=
  (transverseEmbed n).toContinuousLinearMap.adjoint

theorem transverseEmbed_clock {n : ℕ} (x : Transverse n) : transverseEmbed n x 0 = 0 := rfl

theorem transverse_inner {n : ℕ} (u : Transverse n) (x : Space n) :
    ⟪transverseEmbed n u, x⟫_ℝ = ⟪u, transverseProjection n x⟫_ℝ :=
  ((transverseEmbed n).toContinuousLinearMap.adjoint_inner_right u x).symm

theorem transverseProjection_embed {n : ℕ} (u : Transverse n) :
    transverseProjection n (transverseEmbed n u) = u := by
  apply ext_inner_left ℝ
  intro v
  rw [← transverse_inner, (transverseEmbed n).inner_map_map]

theorem transverseProjection_norm_le {n : ℕ} (x : Space n) :
    ‖transverseProjection n x‖ ≤ ‖x‖ := by
  have hi := transverse_inner (transverseProjection n x) x
  rw [real_inner_self_eq_norm_sq] at hi
  have hn := real_inner_le_norm (transverseEmbed n (transverseProjection n x)) x
  rw [(transverseEmbed n).norm_map, hi] at hn
  nlinarith [norm_nonneg (transverseProjection n x), norm_nonneg x]

theorem roomMeasurement_continuous {n : ℕ} (ρ lam : ℝ) :
    Continuous (fun cx : Space n × Space n => roomMeasurement ρ lam cx.1 cx.2) := by
  have hc := (cutoff_smooth n).continuous
  unfold roomMeasurement
  fun_prop

theorem transverse_room_measurement {n : ℕ} (ρ lam σ : ℝ)
    (c x : Space n) (u z : Transverse n) :
    ⟪transverseEmbed n u + σ • transverseEmbed n z, roomMeasurement ρ lam c x⟫_ℝ =
      ⟪u + σ • z, transverseProjection n (roomMeasurement ρ lam c x)⟫_ℝ := by
  rw [← map_smul, ← map_add, transverse_inner]

end NCBall
