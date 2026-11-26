import MinimaxAudit.HardPotential
import MinimaxAudit.IdealWitness

/-! Actual uniform potential comparison on paired Euclidean frames. -/
open scoped RealInnerProductSpace
namespace MinimaxAudit

theorem orthonormal_sum_abs_inner_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {W : I → E}
    (hW : Orthonormal ℝ W) (z : E) :
    (∑ i, |inner ℝ (W i) z|) ≤ Real.sqrt (Fintype.card I) * ‖z‖ := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun _ => (1 : ℝ)) (fun i => |inner ℝ (W i) z|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hc
  have hb := hW.sum_inner_products_le z (s := Finset.univ)
  simp only [Real.norm_eq_abs] at hb
  have hcard : (0 : ℝ) ≤ Fintype.card I := by positivity
  have hsq : (Real.sqrt (Fintype.card I) * ‖z‖) ^ 2 =
      (Fintype.card I : ℝ) * ‖z‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hcard]
  have hm := mul_le_mul_of_nonneg_left hb hcard
  have hs : 0 ≤ ∑ i, |inner ℝ (W i) z| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hr := mul_nonneg (Real.sqrt_nonneg (Fintype.card I)) (norm_nonneg z)
  nlinarith

theorem signedQuadratic_eq_witnessBase {dx dy : ℕ} (z : SaddleSpace dx dy) :
    signedQuadratic (euclideanSaddleSign dx dy) z = witnessBase (primalBlock z) (dualBlock z) := by
  unfold signedQuadratic
  rw [saddle_sign_blocks, ← join_blocks z, join_blocks_inner]
  simp only [primal_join, dual_join, inner_neg_left, real_inner_self_eq_norm_sq]
  unfold witnessBase
  ring

theorem minimaxHardPotential_eq_source {n dx dy : ℕ} (profile : GateProfile)
    (tau lam q c : ℝ) {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) :
    minimaxHardPotential profile tau lam q c hU hV =
      chainPotential profile tau lam c q (fun z => witnessBase (primalBlock z) (dualBlock z))
        (pairedA U V) (pairedB U V) := by
  rw [source_chainPotential_eq_block profile tau lam q c _ hU hV]
  funext z
  simp only [minimaxHardPotential, framedHardPotential, signedQuadratic_eq_witnessBase]

noncomputable def approximationFrameIndex (n : ℕ) (i : Fin (n+1)) : Fin (n+1) × Fin 2 :=
  (i, if i = Fin.last n then 0 else 1)

theorem approximationFrameIndex_injective (n : ℕ) : Function.Injective (approximationFrameIndex n) := by
  intro i j h
  exact congrArg Prod.fst h

theorem approximation_coordinates_sum {n dx dy : ℕ}
    (U : Fin (n+1) → Primal dx) (V : Fin (n+1) → Dual dy) (z : SaddleSpace dx dy) :
    (∑ j : Fin (n+1), |inner ℝ (blockPairedFrame U V (approximationFrameIndex n j)) z|) =
      (∑ i : Fin n, |pairedB U V i.succ z|) + |pairedA U V (Fin.last n) z| := by
  rw [Fin.sum_univ_castSucc]
  have hi (i : Fin n) : i.castSucc ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp [approximationFrameIndex, hi, blockPairedFrame_first, blockPairedFrame_second,
    finRotate_castSucc_source, pairedA, pairedB, innerSL_apply_apply]

theorem approximation_coordinates_bound {n dx dy : ℕ}
    {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (z : SaddleSpace dx dy) :
    (∑ i : Fin n, |pairedB U V i.succ z|) + |pairedA U V (Fin.last n) z| ≤
      Real.sqrt (n+1) * ‖z‖ := by
  have hf := (blockPairedFrame_orthonormal hU hV).comp (approximationFrameIndex n)
    (approximationFrameIndex_injective n)
  have hb := orthonormal_sum_abs_inner_le hf z
  simpa [Function.comp_def, approximation_coordinates_sum] using hb

theorem minimaxHardPotential_ideal_approximation {n dx dy : ℕ}
    (profile : GateProfile) {tau lam q : ℝ} (htau : 0 < tau)
    (hlam : 0 ≤ lam) (hq : 0 ≤ q) (c : ℝ)
    {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) (z : SaddleSpace dx dy) :
    |minimaxHardPotential profile tau lam q c hU hV z - idealHardPotential lam q c U V z| ≤
      lam * q * tau * Real.sqrt (n+1) * ‖z‖ := by
  rw [minimaxHardPotential_eq_source profile tau lam q c hU hV]
  let a := pairedA U V
  let b := pairedB U V
  have heq :
      chainPotential profile tau lam c q (fun z => witnessBase (primalBlock z) (dualBlock z)) a b z -
        idealHardPotential lam q c U V z =
      -lam * q * ((∑ i : Fin n,
        (scalarGate profile tau (a i.castSucc z) (b i.succ z) - a i.castSucc z * b i.succ z)) +
        (doubleGate profile tau (a (Fin.last n) z) - (a (Fin.last n) z) ^ 2 / 2)) := by
    unfold chainPotential idealHardPotential idealScalarValue
    dsimp only
    rw [Finset.sum_sub_distrib]
    change _ = _
    dsimp only [a,b]
    ring
  change |chainPotential profile tau lam c q (fun z => witnessBase (primalBlock z) (dualBlock z)) a b z -
      idealHardPotential lam q c U V z| ≤ _
  rw [heq, abs_mul, abs_mul, abs_neg, abs_of_nonneg hlam, abs_of_nonneg hq]
  have herror :
      |(∑ i : Fin n,
        (scalarGate profile tau (a i.castSucc z) (b i.succ z) - a i.castSucc z * b i.succ z)) +
        (doubleGate profile tau (a (Fin.last n) z) - (a (Fin.last n) z) ^ 2 / 2)| ≤
      tau * ((∑ i : Fin n, |b i.succ z|) + |a (Fin.last n) z|) := by
    calc
      _ ≤ |∑ i : Fin n,
          (scalarGate profile tau (a i.castSucc z) (b i.succ z) - a i.castSucc z * b i.succ z)| +
          |doubleGate profile tau (a (Fin.last n) z) - (a (Fin.last n) z) ^ 2 / 2| := abs_add_le _ _
      _ ≤ (∑ i : Fin n, |scalarGate profile tau (a i.castSucc z) (b i.succ z) -
            a i.castSucc z * b i.succ z|) + tau * |a (Fin.last n) z| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (doubleGate_quadratic_error profile htau _)
      _ ≤ (∑ i : Fin n, tau * |b i.succ z|) + tau * |a (Fin.last n) z| := by
        exact add_le_add (Finset.sum_le_sum (fun i _ => scalarGate_bilinear_error profile htau _ _)) le_rfl
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hcoords := approximation_coordinates_bound hU hV z
  change (∑ i : Fin n, |b i.succ z|) + |a (Fin.last n) z| ≤ _ at hcoords
  have ht := mul_le_mul_of_nonneg_left hcoords htau.le
  have he := mul_le_mul_of_nonneg_left (herror.trans ht) (mul_nonneg hlam hq)
  convert he using 1 <;> first | rfl | ring

theorem uniform_product_potential_approximation {n dx dy : ℕ}
    (profile : GateProfile) {tau lam q R : ℝ} (htau : 0 < tau)
    (hlam : 0 ≤ lam) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hR : 0 ≤ R) (c : ℝ)
    {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)
    (x : Primal dx) (y : Dual dy) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    |minimaxHardPotential profile tau lam q c hU hV (joinBlocks x y) -
      idealHardPotential lam q c U V (joinBlocks x y)| ≤
      3 * lam * tau * R * Real.sqrt (n+1) := by
  have hz : ‖joinBlocks x y‖ ≤ 2 * R := by
    rw [join_blocks_embedding_sum]
    exact (norm_add_le _ _).trans (by
      simpa only [(primalEmbedding dx dy).norm_map, (dualEmbedding dx dy).norm_map, two_mul] using add_le_add hx hy)
  have h := minimaxHardPotential_ideal_approximation profile htau hlam hq c hU hV (joinBlocks x y)
  have hh : lam * q * tau * Real.sqrt (n+1) * ‖joinBlocks x y‖ ≤
      lam * tau * Real.sqrt (n+1) * (2 * R) := by
    calc
      _ ≤ lam * 1 * tau * Real.sqrt (n+1) * (2 * R) := by gcongr
      _ = _ := by ring
  have hn : 0 ≤ lam * tau * R * Real.sqrt (n+1) := by positivity
  exact h.trans (hh.trans (by nlinarith))

end MinimaxAudit
