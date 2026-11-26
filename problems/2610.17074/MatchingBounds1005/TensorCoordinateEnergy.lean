import MatchingBounds1005.TensorOracle
import MatchingBounds1005.TensorEnergy
import MatchingBounds1005.TensorJointEnergy

/-! Tensor observation envelopes and stopped signal energy in the actual
finite Euclidean coordinates used by the Gaussian posterior protocol. -/
noncomputable section
open scoped BigOperators InnerProductSpace

namespace MatchingBounds1005.TensorGeometry
open GaussianVector

def coordinateObservation {d : ℕ} (k : ℕ) (W : Submodule ℝ (Vec d)) :
    Submodule ℝ (Vec (Fintype.card (Fin k → Fin d))) :=
  (observationSpace k W).map (tensorCoordinates d k).toLinearEquiv.toLinearMap

theorem channelCoordinates_mem {d k : ℕ} (W : Submodule ℝ (Vec d))
    {x : Vec d} (hx : x ∈ W) (i : Fin d) :
    channelCoordinates k x i ∈ coordinateObservation k W :=
  ⟨channelRow k x i, channelRow_mem k W hx i, rfl⟩

attribute [local irreducible] Submodule.orthogonalProjection

theorem coordinate_rankOne_projection_bound {d k : ℕ} (hk : 1 ≤ k)
    (W : Submodule ℝ (Vec d)) (V : Submodule ℝ (Vec (Fintype.card (Fin k → Fin d))))
    (hV : V ≤ coordinateObservation k W) (b : Vec d) (hb : ‖b‖ = 1) :
    ‖V.orthogonalProjection (tensorCoordinates d k (rankOne k b))‖ ^ 2 ≤
      k * (‖W.orthogonalProjection b‖ ^ 2) ^ (k - 1) := by
  let I := tensorCoordinates d k
  let V' := V.comap I.toLinearEquiv.toLinearMap
  have hV' : V' ≤ observationSpace k W := by
    intro z hz
    obtain ⟨y, hy, heq⟩ := hV hz
    have he : y = z := I.injective heq
    simpa only [he] using hy
  have hmap : V'.map I.toLinearEquiv.toLinearMap = V := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      refine ⟨I.symm z, ?_, I.apply_symm_apply z⟩
      change I (I.symm z) ∈ V
      simpa only [I.apply_symm_apply] using hz
  have he := I.toLinearIsometry.map_orthogonalProjection V' (rankOne k b)
  have hn := congrArg (fun z => ‖z‖) he
  have hp : ‖V.orthogonalProjection (I (rankOne k b))‖ =
      ‖V'.orthogonalProjection (rankOne k b)‖ := by
    rw [← hmap]
    simpa using hn.symm
  rw [hp]
  exact rankOne_projection_bound hk W V' hV' b hb

theorem cumulative_coordinate_rankOne_energy {ι : Type*} {d k : ℕ} (hk : 1 ≤ k)
    (signals : Finset ι) (b : ι → Vec d) (hb : ∀ s ∈ signals, ‖b s‖ = 1)
    (V : ℕ → Submodule ℝ (Vec (Fintype.card (Fin k → Fin d)))) (hV : Monotone V)
    (W : ι → Submodule ℝ (Vec d)) (ell : ι → ℕ) (T : ℕ)
    (hell : ∀ s ∈ signals, ell s ≤ T)
    (hobs : ∀ s ∈ signals, V (ell s) ≤ coordinateObservation k (W s))
    (w θ : ℝ) (hθ : 0 ≤ θ)
    (hangle : ∀ s ∈ signals, ‖(W s).orthogonalProjection (b s)‖ ≤ θ) :
    (∑ t ∈ Finset.range T,
      ‖InnovationEnergy.proj (V (t + 1) ⊓ (V t)ᗮ)
        (w • ∑ s ∈ signals, if t < ell s then tensorCoordinates d k (rankOne k (b s)) else 0)‖ ^ 2) ≤
      k * (signals.card : ℝ) ^ 2 * w ^ 2 * θ ^ (2 * (k - 1)) := by
  have hbnd (s : ι) (hs : s ∈ signals) :
      ‖InnovationEnergy.proj (V (ell s)) (tensorCoordinates d k (rankOne k (b s)))‖ ^ 2 ≤
        k * θ ^ (2 * (k - 1)) := by
    change ‖(V (ell s)).orthogonalProjection _‖ ^ 2 ≤ _
    apply (coordinate_rankOne_projection_bound hk (W s) (V (ell s)) (hobs s hs) (b s) (hb s hs)).trans
    rw [pow_mul]
    gcongr
    exact hangle s hs
  have he := InnovationEnergy.cumulative_hidden_signal_energy signals V hV
    (fun s => tensorCoordinates d k (rankOne k (b s))) w ell T hell
  have hsum : (∑ s ∈ signals,
      ‖InnovationEnergy.proj (V (ell s)) (tensorCoordinates d k (rankOne k (b s)))‖ ^ 2) ≤
      (signals.card : ℝ) * (k * θ ^ (2 * (k - 1))) := by
    calc
      _ ≤ ∑ _s ∈ signals, (k : ℝ) * θ ^ (2 * (k - 1)) := Finset.sum_le_sum hbnd
      _ = _ := by simp
  apply he.trans
  exact (mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (Nat.cast_nonneg signals.card) (sq_nonneg w))).trans_eq (by ring)

end MatchingBounds1005.TensorGeometry
