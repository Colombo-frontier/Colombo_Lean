import Bilevel.EndpointTransportQuadratic
import Bilevel.RadialWrapper

/-!
The actual orthogonally transported, endpoint-coupled quadratic lower problem.
The rotations are arbitrary linear isometric equivalences, so the conclusions
hold on the entire ambient space, independently of any hidden hard frame.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse

open EndpointTransportMatrix

abbrev Block (D : ℕ) := EuclideanSpace ℝ (Fin D)
abbrev Configuration (n D : ℕ) := Index n → Block D
abbrev Rotations (n D : ℕ) := Index n → (Block D ≃ₗᵢ[ℝ] Block D)
abbrev Physical (n D : ℕ) := PiLp 2 (fun _ : Index n => Block D)

def coordinates {n D : ℕ} (Q : Rotations n D) (Y : Configuration n D) (d : Fin D) :
    Index n → ℝ := fun i => ((Q i).symm (Y i)) d

def response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D) (v : Block D) : Configuration n D :=
  fun i => (c/δ * endpointColumn n i) • Q i v

def lower {n D : ℕ} (δ c : ℝ) (Q : Rotations n D) (v : Block D)
    (Y : Configuration n D) : ℝ :=
  ∑ d : Fin D, scalarLower n δ c (v d) (coordinates Q Y d)

def gain (n : ℕ) (δ c : ℝ) : ℝ := c/δ * (2*(n+1:ℝ)^2/3)

/-- The transported matrix action `δ Q (A ⊗ I) Qᵀ` on actual blocks. -/
def hessianAction {n D : ℕ} (δ : ℝ) (Q : Rotations n D)
    (Y : Configuration n D) : Configuration n D :=
  fun i => δ • Q i (∑ j : Index n, matrix n i j • (Q j).symm (Y j))

theorem hessianAction_coordinates {n D : ℕ} (δ : ℝ) (Q : Rotations n D)
    (Y : Configuration n D) (d : Fin D) (i : Index n) :
    coordinates Q (hessianAction δ Q Y) d i =
      δ * (matrix n).mulVec (coordinates Q Y d) i := by
  simp only [coordinates, hessianAction, map_smul,
    LinearIsometryEquiv.symm_apply_apply, PiLp.smul_apply, smul_eq_mul]
  congr 1
  change (PiLp.projₗ 2 (𝕜 := ℝ) (fun _ : Fin D => ℝ) d)
    (∑ j : Index n, matrix n i j • (Q j).symm (Y j)) = _
  rw [map_sum]
  rfl

theorem response_coordinates {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (v : Block D) (d : Fin D) :
    coordinates Q (response δ c Q v) d = scalarResponse n δ c (v d) := by
  funext i
  simp [coordinates, response, scalarResponse, map_smul, mul_assoc, mul_comm, mul_left_comm]

theorem response_solves_system {n D : ℕ} {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ)
    (Q : Rotations n D) (v : Block D) :
    hessianAction δ Q (response δ c Q v) =
      fun i => (c * lastUnit n i) • Q i v := by
  funext i
  apply (Q i).symm.injective
  ext d
  change coordinates Q (hessianAction δ Q (response δ c Q v)) d i = _
  rw [hessianAction_coordinates, response_coordinates, scalarResponse_equation]
  simp only [map_smul, LinearIsometryEquiv.symm_apply_apply, PiLp.smul_apply,
    smul_eq_mul, Pi.smul_apply]
  field_simp
  ring

/-- This is the source's actual quadratic objective in physical coordinates.
For the source convention `Q_last = identity`, its last term is `-c <v,Y_last>`. -/
theorem lower_physical_formula {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (v : Block D) (Y : Configuration n D) :
    lower δ c Q v Y =
      δ/2 * (∑ d : Fin D, quadratic n (matrix n) (coordinates Q Y d)) -
        c * ⟪Q (Fin.last (n+1)) v, Y (Fin.last (n+1))⟫ := by
  rw [LinearIsometryEquiv.inner_map_eq_flip, PiLp.inner_apply]
  simp only [RCLike.inner_apply', conj_trivial]
  unfold lower scalarLower
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  unfold coordinates
  ring

/-- Global optimality of the explicit response in the actual transported
finite-dimensional lower objective, without assuming stationarity or convexity. -/
theorem response_minimum {n D : ℕ} {δ : ℝ} (hδ : 0 < δ) (c : ℝ)
    (Q : Rotations n D) (v : Block D) (Y : Configuration n D) :
    lower δ c Q v (response δ c Q v) ≤ lower δ c Q v Y := by
  unfold lower
  simp only [response_coordinates]
  apply Finset.sum_le_sum
  intro d _
  exact scalarLower_minimum n hδ c (v d) (coordinates Q Y d)

/-- The lower objective has exactly one minimizer, at the displayed response. -/
theorem lower_eq_min_iff {n D : ℕ} {δ : ℝ} (hδ : 0 < δ) (c : ℝ)
    (Q : Rotations n D) (v : Block D) (Y : Configuration n D) :
    lower δ c Q v Y = lower δ c Q v (response δ c Q v) ↔ Y = response δ c Q v := by
  constructor
  · intro he
    have hg (d : Fin D) : 0 ≤ scalarLower n δ c (v d) (coordinates Q Y d) -
        scalarLower n δ c (v d) (scalarResponse n δ c (v d)) :=
      sub_nonneg.mpr (scalarLower_minimum n hδ c (v d) (coordinates Q Y d))
    have hs : (∑ d : Fin D, (scalarLower n δ c (v d) (coordinates Q Y d) -
        scalarLower n δ c (v d) (scalarResponse n δ c (v d)))) = 0 := by
      rw [Finset.sum_sub_distrib]
      unfold lower at he
      simp only [response_coordinates] at he
      exact sub_eq_zero.mpr he
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => hg d)).mp hs
    have hcoord (d : Fin D) : coordinates Q Y d = scalarResponse n δ c (v d) :=
      (scalarLower_eq_min_iff n hδ c (v d) (coordinates Q Y d)).mp
        (sub_eq_zero.mp (hz d (Finset.mem_univ d)))
    funext i
    apply (Q i).symm.injective
    ext d
    have h1 := congrFun (hcoord d) i
    have h2 := congrFun (response_coordinates δ c Q v d) i
    exact h1.trans h2.symm
  · intro he
    rw [he]

/-- The source's endpoint identities before imposing `Q_last = identity`. -/
theorem response_endpoints {n D : ℕ} (δ c : ℝ) (Q : Rotations n D) (v : Block D) :
    (2:ℝ) • (Q 0).symm (response δ c Q v 0) = gain n δ c • v ∧
      response δ c Q v (Fin.last (n+1)) = gain n δ c • Q (Fin.last (n+1)) v := by
  constructor
  · simp only [response, map_smul, LinearIsometryEquiv.symm_apply_apply,
      endpointColumn_first, smul_smul]
    unfold gain
    congr 1
    ring
  · simp only [response, endpointColumn_last, gain]

def physicalResponse {n D : ℕ} (δ c : ℝ) (Q : Rotations n D) (v : Block D) : Physical n D :=
  (WithLp.equiv 2 _).symm (response δ c Q v)

theorem physicalResponse_norm_sq {n D : ℕ} (δ c : ℝ) (Q : Rotations n D) (v : Block D) :
    ‖physicalResponse δ c Q v‖^2 = gamma n ^ 2 * gain n δ c ^ 2 * ‖v‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  have hnorm (i : Index n) : ‖physicalResponse δ c Q v i‖^2 =
      (c/δ)^2 * endpointColumn n i ^ 2 * ‖v‖^2 := by
    change ‖(c/δ * endpointColumn n i) • Q i v‖^2 = _
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, LinearIsometryEquiv.norm_map,
      mul_pow]
  simp_rw [hnorm]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hg : gamma n ^ 2 * (2*(n+1:ℝ)^2/3)^2 =
      ∑ i : Index n, endpointColumn n i ^ 2 := by
    rw [gamma, div_pow, euclideanColumn_norm_sq]
    apply div_mul_cancel₀
    positivity
  rw [← hg]
  unfold gain
  ring

theorem gamma_positive (n : ℕ) : 0 < gamma n := by
  have hn : 0 ≤ gamma n := by unfold gamma; positivity
  have hb := (gamma_sq_bounds n).1
  nlinarith

/-- The full-vector norm identity includes all ambient coordinates. -/
theorem physicalResponse_norm {n D : ℕ} {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    (Q : Rotations n D) (v : Block D) :
    ‖physicalResponse δ c Q v‖ = gamma n * gain n δ c * ‖v‖ := by
  have hsq := physicalResponse_norm_sq δ c Q v
  have hg : 0 ≤ gain n δ c := by unfold gain; positivity
  have hp := (gamma_positive n).le
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith

end Bilevel.EndpointTransportResponse
