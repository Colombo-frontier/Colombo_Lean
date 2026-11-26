import MatchingBounds1005.TensorGeometry
import MatchingBounds1005.InnovationEnergy

/-! Actual rank-one signals in the telescoping innovation bound. -/
noncomputable section
open scoped BigOperators

namespace MatchingBounds1005.TensorGeometry
attribute [local irreducible] Submodule.orthogonalProjection

theorem cumulative_rankOne_energy {ι : Type*} {d k : ℕ} (hk : 1 ≤ k)
    (signals : Finset ι) (b : ι → Vec d) (hb : ∀ s ∈ signals, ‖b s‖ = 1)
    (V : ℕ → Submodule ℝ (Tensor d k)) (hV : Monotone V)
    (W : ι → Submodule ℝ (Vec d)) (ell : ι → ℕ) (T : ℕ)
    (hell : ∀ s ∈ signals, ell s ≤ T)
    (hobs : ∀ s ∈ signals, V (ell s) ≤ observationSpace k (W s))
    (w θ : ℝ) (hθ : 0 ≤ θ)
    (hangle : ∀ s ∈ signals, ‖(W s).orthogonalProjection (b s)‖ ≤ θ) :
    (∑ t ∈ Finset.range T,
      ‖InnovationEnergy.proj (V (t + 1) ⊓ (V t)ᗮ)
        (w • ∑ s ∈ signals, if t < ell s then rankOne k (b s) else 0)‖ ^ 2) ≤
      k * (signals.card : ℝ) ^ 2 * w ^ 2 * θ ^ (2 * (k - 1)) := by
  have hbnd (s : ι) (hs : s ∈ signals) :
      ‖InnovationEnergy.proj (V (ell s)) (rankOne k (b s))‖ ^ 2 ≤
        k * θ ^ (2 * (k - 1)) := by
    change ‖(V (ell s)).orthogonalProjection (rankOne k (b s))‖ ^ 2 ≤ _
    apply (rankOne_projection_bound hk (W s) (V (ell s)) (hobs s hs) (b s) (hb s hs)).trans
    rw [pow_mul]
    gcongr
    exact hangle s hs
  have he := InnovationEnergy.cumulative_hidden_signal_energy signals V hV
    (fun s => rankOne k (b s)) w ell T hell
  have hsum : (∑ s ∈ signals, ‖InnovationEnergy.proj (V (ell s)) (rankOne k (b s))‖ ^ 2) ≤
      (signals.card : ℝ) * (k * θ ^ (2 * (k - 1))) := by
    calc
      _ ≤ ∑ _s ∈ signals, (k : ℝ) * θ ^ (2 * (k - 1)) :=
        Finset.sum_le_sum hbnd
      _ = _ := by simp
  apply he.trans
  exact (mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (Nat.cast_nonneg signals.card) (sq_nonneg w))).trans_eq (by ring)

end MatchingBounds1005.TensorGeometry
