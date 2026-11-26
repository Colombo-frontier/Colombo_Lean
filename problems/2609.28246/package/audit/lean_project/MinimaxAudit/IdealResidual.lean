import MinimaxAudit.SourceGeometry
import MinimaxAudit.IdealWitness
import MinimaxAudit.PotentialApproximation

/-! Ideal residual obstruction for the genuine signed gradient of the actual
quadratic ideal scalar potential, rather than an abstract residual sequence. -/
open scoped RealInnerProductSpace
namespace MinimaxAudit
set_option maxHeartbeats 1000000
section Ideal
variable {n dx dy : ℕ} {U : Fin (n+1) → Primal dx} {V : Fin (n+1) → Dual dy}

noncomputable def idealScalarDerivative (lam q c : ℝ) (z : SaddleSpace dx dy) :
    SaddleSpace dx dy →L[ℝ] ℝ :=
  lam • (innerSL ℝ (euclideanSaddleSign dx dy z) - c • pairedB U V 0 -
    q • (∑ i : Fin n, ((pairedB U V i.succ z) • pairedA U V i.castSucc +
      (pairedA U V i.castSucc z) • pairedB U V i.succ)) -
    (q * pairedA U V (Fin.last n) z) • pairedA U V (Fin.last n))

theorem idealHardPotential_hasFDerivAt (lam q c : ℝ) (z : SaddleSpace dx dy) :
    HasFDerivAt (idealHardPotential lam q c U V) (idealScalarDerivative (U := U) (V := V) lam q c z) z := by
  have hb := signedQuadratic_hasFDerivAt (euclideanSaddleSign dx dy)
    (euclideanSaddleSign_involutive dx dy) z
  have hs := ((pairedB U V 0).hasFDerivAt (x := z)).const_mul c
  have he (i : Fin n) := ((pairedA U V i.castSucc).hasFDerivAt (x := z)).mul
    ((pairedB U V i.succ).hasFDerivAt (x := z))
  have heSum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => he i)
  have ht := (((pairedA U V (Fin.last n)).hasFDerivAt (x := z)).pow 2).const_mul (q / 2)
  have h := (((hb.sub hs).sub (heSum.const_mul q)).sub ht).const_mul lam
  convert! h using 1
  · ext w
    simp only [idealHardPotential, idealScalarValue, Pi.sub_apply, Pi.mul_apply, signedQuadratic_eq_witnessBase]
  · ext w
    simp [idealScalarDerivative, ContinuousLinearMap.sum_apply, Finset.sum_add_distrib]
    all_goals ring
    all_goals simp

variable (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)
include hU hV

theorem pairedA_ideal_operator (lam q c : ℝ) (z : SaddleSpace dx dy) (i : Fin (n+1)) :
    pairedA U V i (scalarSaddleOperator (idealHardPotential lam q c U V) z) =
      lam * idealError q c (sourceANat (U := U) (V := V) z) i.val := by
  have hA (j : Fin (n+1)) : pairedA U V j (pairedMinus U V i) = 0 := by
    exact (paired_frame_orthonormal hU hV).inner_eq_zero (by simp : (Sum.inl j : Fin (n+1) ⊕ Fin (n+1)) ≠ Sum.inr i)
  have hB (j : Fin (n+1)) : pairedB U V j (pairedMinus U V i) = if j = i then 1 else 0 := by
    simpa [pairedB, pairedFrame] using
      (orthonormal_iff_ite.mp ((paired_frame_orthonormal hU hV).comp Sum.inr Sum.inr_injective) j i)
  have hbase : inner ℝ (euclideanSaddleSign dx dy z) (pairedMinus U V i) = pairedA U V i z := by
    rw [real_inner_comm, inner_euclideanSaddleSign_swap, saddle_sign_paired_minus]
    rfl
  change inner ℝ (pairedPlus U V i) (euclideanSaddleSign dx dy (gradient _ z)) = _
  rw [inner_euclideanSaddleSign_swap, saddle_sign_paired_plus, real_inner_comm,
    inner_gradient_left, (idealHardPotential_hasFDerivAt lam q c z).fderiv]
  simp only [idealScalarDerivative, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, innerSL_apply_apply, smul_eq_mul,
    hA, hB, hbase, mul_zero, zero_add, sub_zero]
  by_cases hi : i.val = 0
  · have hieq : i = 0 := Fin.ext hi
    subst i
    have hi0 (j : Fin n) : j.succ ≠ (0 : Fin (n+1)) := by intro h; have := congrArg Fin.val h; simp at this
    simp [hi0, idealError, sourceANat]
  · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have hklt : k < n := by omega
    let j : Fin n := ⟨k,hklt⟩
    have hieq : i = j.succ := Fin.ext hk
    subst i
    have hz : (0 : Fin (n+1)) ≠ j.succ := by intro heq; have := congrArg Fin.val heq; simp at this
    have hj (t : Fin n) : t.succ = j.succ ↔ t = j := Fin.succ_inj
    try simp only [hz, if_false, mul_zero, sub_zero]
    simp_rw [hj]
    try simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [idealError, sourceANat, j, hklt, show k < n+1 by omega]

theorem ideal_residual_source {lam q c rho : ℝ} (hlam : 0 ≤ lam)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (z : SaddleSpace dx dy)
    (hr : |pairedA U V (Fin.last n) z| ≤ rho) :
    lam * ((q ^ n * c - rho) / Real.sqrt (n+1)) ≤
      ‖scalarSaddleOperator (idealHardPotential lam q c U V) z‖ := by
  let F := scalarSaddleOperator (idealHardPotential lam q c U V) z
  have htel : (∑ j ∈ Finset.range (n+1), q ^ (n-j) * sourceANat (U := U) (V := V) F j) =
      lam * (pairedA U V (Fin.last n) z - q ^ n * c) := by
    calc
      _ = lam * ∑ j ∈ Finset.range (n+1), q ^ (n-j) * idealError q c (sourceANat (U := U) (V := V) z) j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < n+1 := Finset.mem_range.mp hj
        rw [show sourceANat (U := U) (V := V) F j = pairedA U V ⟨j,hjlt⟩ F by simp [sourceANat, hjlt]]
        rw [pairedA_ideal_operator hU hV]
        ring
      _ = _ := by
        rw [ideal_chain_telescoping]
        have heq : (⟨n, by omega⟩ : Fin (n+1)) = Fin.last n := Fin.ext rfl
        simp [sourceANat, heq]
  have hw := weighted_error_abs_le q hq0 hq1 (sourceANat (U := U) (V := V) F) n
  have hb : Real.sqrt (∑ j ∈ Finset.range (n+1), sourceANat (U := U) (V := V) F j ^ 2) ≤ ‖F‖ := by
    rw [Finset.sum_range]
    simp_rw [sourceANat_fin]
    apply Real.sqrt_le_iff.mpr
    refine ⟨norm_nonneg _, ?_⟩
    have hplus := (paired_frame_orthonormal hU hV).comp Sum.inl Sum.inl_injective
    simpa [pairedA, pairedFrame, innerSL_apply_apply, Real.norm_eq_abs, sq_abs] using
      hplus.sum_inner_products_le F (s := Finset.univ)
  rw [htel] at hw
  have hnorm := hw.trans (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _))
  have ha := (le_abs_self (pairedA U V (Fin.last n) z)).trans hr
  have hneg := neg_le_abs (lam * (pairedA U V (Fin.last n) z - q ^ n * c))
  have hlow : lam * (q ^ n * c - rho) ≤ Real.sqrt (n+1) * ‖F‖ := by
    have hm := mul_le_mul_of_nonneg_left ha hlam
    nlinarith only [hnorm,hneg,hm]
  have hn : (0 : ℝ) < Real.sqrt (n+1) := Real.sqrt_pos.2 (by positivity)
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hn).2 (by simpa [mul_comm] using hlow)
end Ideal
end MinimaxAudit
