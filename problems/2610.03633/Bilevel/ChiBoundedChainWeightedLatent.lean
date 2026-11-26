import Bilevel.ChiBoundedChainPayload

/-! Actual weighted latent objective and release term from the local
certificate. These are definitions and derivative identities, not hypotheses
postulating the certificate's conclusion. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiBoundedChain

theorem releaseGate_hasDerivAt (t : ℝ) :
    HasDerivAt releaseGate (deriv Real.smoothTransition (t-1)) t := by
  convert ((Real.smoothTransition.contDiff (n:=1)).differentiable (by norm_num) (t-1)).hasDerivAt.comp t
    ((hasDerivAt_id t).sub_const 1) using 1
  simp

theorem releaseGate_deriv_nonneg (t : ℝ) : 0≤deriv releaseGate t := by
  rw [(releaseGate_hasDerivAt t).deriv]
  exact transition_deriv_nonneg _

theorem releaseGate_deriv_zero {t : ℝ} (ht : t≤1) : deriv releaseGate t=0 :=
  ZeroChainResidualCutoffs.deriv_zero_of_constant_on
    ((releaseGate_contDiff (k:=1)).differentiable (by norm_num) t)
    (uniqueDiffOn_Iic 1) (fun _ hs => releaseGate_zero hs) ht

def weightedLatent (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ) (z : Space n) : ℝ :=
  w*payload n ℓ h A ν g hp T z+Rp*releaseGate (z (Fin.last n)/hp)

def releaseCoefficient (hp Rp t : ℝ) : ℝ := Rp*deriv releaseGate (t/hp)/hp

theorem weightedLatent_hasGradientAt (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ) (z : Space n) :
    HasGradientAt (weightedLatent n ℓ h A ν g hp T w Rp)
      (w • gradient (payload n ℓ h A ν g hp T) z+
        releaseCoefficient hp Rp (z (Fin.last n)) • basis (Fin.last n)) z := by
  have hpayload := (payload_hasGradientAt n ℓ h A ν g hp T z).differentiableAt.hasGradientAt
  have h₀ := hpayload.hasFDerivAt.const_mul w
  have hrel : HasDerivAt (fun t : ℝ => Rp*releaseGate (t/hp))
      (releaseCoefficient hp Rp (z (Fin.last n))) (z (Fin.last n)) := by
    have hh := ((((releaseGate_contDiff (k:=1)).differentiable (by norm_num) (z (Fin.last n)/hp)).hasDerivAt).comp
      (z (Fin.last n)) ((hasDerivAt_id _).div_const hp)).const_mul Rp
    convert hh using 1
    unfold releaseCoefficient
    ring
  have h₁ := terminal_hasGradientAt z hrel
  apply hasGradientAt_iff_hasFDerivAt.mpr
  change HasFDerivAt (fun x => w*payload n ℓ h A ν g hp T x+Rp*releaseGate (x (Fin.last n)/hp)) _ z
  simpa only [map_add,map_smul] using h₀.add h₁.hasFDerivAt

theorem weightedLatent_gradient (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ) (z : Space n) :
    gradient (weightedLatent n ℓ h A ν g hp T w Rp) z=
      w • gradient (payload n ℓ h A ν g hp T) z+
        releaseCoefficient hp Rp (z (Fin.last n)) • basis (Fin.last n) :=
  (weightedLatent_hasGradientAt n ℓ h A ν g hp T w Rp z).gradient

theorem releaseCoefficient_nonpos (hp Rp t : ℝ) (hhp : 0<hp) (hRp : Rp≤0) :
    releaseCoefficient hp Rp t≤0 :=
  div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hRp (releaseGate_deriv_nonneg _)) hhp.le

theorem weightedLatent_coord_le_payload (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ)
    (hhp : 0<hp) (hRp : Rp≤0) (z : Space n) (j : Fin (n+1)) :
    gradient (weightedLatent n ℓ h A ν g hp T w Rp) z j≤
      w*gradient (payload n ℓ h A ν g hp T) z j := by
  rw [weightedLatent_gradient,PiLp.add_apply,PiLp.smul_apply,PiLp.smul_apply,smul_eq_mul,smul_eq_mul]
  have hb : 0≤basis (Fin.last n) j := by simp [basis];split_ifs <;> norm_num
  exact add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg (releaseCoefficient_nonpos hp Rp _ hhp hRp) hb)

theorem weightedLatent_coord_le_chain (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) (hw : 0≤w) (hRp : Rp≤0)
    (z : Space n) (j : Fin (n+1)) :
    gradient (weightedLatent n ℓ h A ν g hp T w Rp) z j≤w*gradient (chain n ℓ h) z j :=
  (weightedLatent_coord_le_payload n ℓ h A ν g hp T w Rp hhp hRp z j).trans
    (mul_le_mul_of_nonneg_left (payload_gradient_coord_le_chain n ℓ h A ν g hp T hA hν hg hh z j) hw)

theorem weightedLatent_gradient_nonpos (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) (hw : 0≤w) (hRp : Rp≤0)
    (z : Space n) (j : Fin (n+1)) :
    gradient (weightedLatent n ℓ h A ν g hp T w Rp) z j≤0 :=
  (weightedLatent_coord_le_chain n ℓ h A ν g hp T w Rp hA hν hg hh hhp hw hRp z j).trans
    (mul_nonpos_of_nonneg_of_nonpos hw (chain_gradient_nonpos n ℓ h hℓ hh z j))

theorem chain_frontier (n : ℕ) (ℓ h : ℝ) (hℓ : 0≤ℓ) (hh : 0<h) (z : Space n)
    (hz : |z (Fin.last n)|<h) :
    ∃ j : Fin (n+1),|z j|<h ∧ gradient (chain n ℓ h) z j≤-(ℓ*h) := by
  classical
  let s := Finset.univ.filter (fun j : Fin (n+1) => |z j|<h)
  have hs : s.Nonempty := ⟨Fin.last n,by simp [s,hz]⟩
  let j := s.min' hs
  have hj : |z j|<h := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  have hsmall : |(h⁻¹ • z) j|<1 := by
    simp only [PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hh)]
    exact (inv_mul_lt_iff₀ hh).mpr (by simpa using hj)
  have hprev (i : Fin (n+1)) (hij : i<j) : 1≤|(h⁻¹ • z) i| := by
    have hi : h≤|z i| := by
      by_contra hi
      have himem : i∈s := by simp [s,lt_of_not_ge hi]
      exact (not_lt_of_ge (Finset.min'_le s i himem)) hij
    simp only [PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hh)]
    exact (le_inv_mul_iff₀ hh).mpr (by simpa using hi)
  have hd := coordinate_endgame n (h⁻¹ • z) j hsmall hprev
  refine ⟨j,hj,?_⟩
  rw [chain_gradient n ℓ h hh,PiLp.smul_apply,smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hd (mul_nonneg hℓ hh.le)]

theorem weightedLatent_frontier (n : ℕ) (ℓ h A ν g hp T w Rp : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hhp : 0<hp) (hw : 0≤w) (hRp : Rp≤0)
    (z : Space n) (hz : |z (Fin.last n)|<h) :
    ∃ j : Fin (n+1),|z j|<h ∧ gradient (weightedLatent n ℓ h A ν g hp T w Rp) z j≤-(w*(ℓ*h)) := by
  obtain ⟨j,hj,hgrad⟩ := chain_frontier n ℓ h hℓ hh z hz
  refine ⟨j,hj,?_⟩
  have hc := weightedLatent_coord_le_chain n ℓ h A ν g hp T w Rp hA hν hg hh hhp hw hRp z j
  nlinarith [mul_le_mul_of_nonneg_left hgrad hw]

end Bilevel.ChiBoundedChain
