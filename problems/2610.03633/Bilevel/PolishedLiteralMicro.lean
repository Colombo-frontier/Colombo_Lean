import Bilevel.PolishedLiteralMacro

/-! The literal positive-terminal-receiver micro core in `lem:micro`.
The chain uses the manuscript's exact exponential Psi. The receiver and
release use actual C-infinity smooth-transition profiles allowed by the
manuscript; there is no extra negative receiver. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.PolishedLiteral
open ChiBoundedChain RadialWrapper ZeroChainPotential

/-- The unwrapped micro core with its fixed macro weight and residual. -/
def microLatent (n : ℕ) (ℓ h A ν g b w r : ℝ) (z : Space n) : ℝ :=
  w*chain n ℓ h z+
    (w*positiveReceiver A ν g h b (z (Fin.last n))+r*releaseGate (z (Fin.last n)/b))

theorem microLatent_hasGradientAt (n : ℕ) (ℓ h A ν g b w r : ℝ) (z : Space n) :
    HasGradientAt (microLatent n ℓ h A ν g b w r)
      (w • gradient (chain n ℓ h) z+
        (w*positiveReceiverSlope A ν g h b (z (Fin.last n))+
          releaseCoefficient b r (z (Fin.last n))) • basis (Fin.last n)) z := by
  have hc := ((chain_contDiff n ℓ h 1).differentiable (by norm_num) z).hasGradientAt
  have hd := (positiveReceiver_hasDerivAt A ν g h b (z (Fin.last n))).const_mul w
  have hq : HasDerivAt (fun t : ℝ => r*releaseGate (t/b))
      (releaseCoefficient b r (z (Fin.last n))) (z (Fin.last n)) := by
    have hh := ((((releaseGate_contDiff (k:=1)).differentiable (by norm_num)
      (z (Fin.last n)/b)).hasDerivAt).comp (z (Fin.last n))
      ((hasDerivAt_id _).div_const b)).const_mul r
    convert hh using 1
    unfold releaseCoefficient
    ring
  have ht := terminal_hasGradientAt z (hd.add hq)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  change HasFDerivAt (fun x => w*chain n ℓ h x+
    (w*positiveReceiver A ν g h b (x (Fin.last n))+r*releaseGate (x (Fin.last n)/b))) _ z
  simpa only [map_add,map_smul] using (hc.hasFDerivAt.const_mul w).add ht.hasFDerivAt

theorem microLatent_gradient (n : ℕ) (ℓ h A ν g b w r : ℝ) (z : Space n) :
    gradient (microLatent n ℓ h A ν g b w r) z=
      w • gradient (chain n ℓ h) z+
        (w*positiveReceiverSlope A ν g h b (z (Fin.last n))+
          releaseCoefficient b r (z (Fin.last n))) • basis (Fin.last n) :=
  (microLatent_hasGradientAt n ℓ h A ν g b w r z).gradient

theorem microLatent_coord_le_chain (n : ℕ) (ℓ h A ν g b w r : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hb : 0<b)
    (hw : 0≤w) (hr : r≤0) (z : Space n) (j : Fin (n+1)) :
    gradient (microLatent n ℓ h A ν g b w r) z j≤w*gradient (chain n ℓ h) z j := by
  rw [microLatent_gradient,PiLp.add_apply,PiLp.smul_apply,PiLp.smul_apply,smul_eq_mul,smul_eq_mul]
  have hs := positiveReceiverSlope_nonpos A ν g h b (z (Fin.last n)) hA hν hg hh
  have hq := releaseCoefficient_nonpos b r (z (Fin.last n)) hb hr
  have he : w*positiveReceiverSlope A ν g h b (z (Fin.last n))+
      releaseCoefficient b r (z (Fin.last n))≤0 :=
    add_nonpos (mul_nonpos_of_nonneg_of_nonpos hw hs) hq
  have hbas : 0≤basis (Fin.last n) j := by simp [basis];split_ifs <;> norm_num
  exact add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg he hbas)

theorem microLatent_nonpos (n : ℕ) (ℓ h A ν g b w r : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hb : 0<b)
    (hw : 0≤w) (hr : r≤0) (z : Space n) (j : Fin (n+1)) :
    gradient (microLatent n ℓ h A ν g b w r) z j≤0 :=
  (microLatent_coord_le_chain n ℓ h A ν g b w r hA hν hg hh hb hw hr z j).trans
    (mul_nonpos_of_nonneg_of_nonpos hw (chain_gradient_nonpos n ℓ h hℓ hh z j))

theorem microLatent_terminal_le_receiver (n : ℕ) (ℓ h A ν g b w r : ℝ)
    (hℓ : 0≤ℓ) (hh : 0<h) (hb : 0<b) (hw : 0≤w) (hr : r≤0) (z : Space n) :
    gradient (microLatent n ℓ h A ν g b w r) z (Fin.last n)≤
      w*positiveReceiverSlope A ν g h b (z (Fin.last n)) := by
  rw [microLatent_gradient,PiLp.add_apply,PiLp.smul_apply,PiLp.smul_apply,smul_eq_mul,smul_eq_mul]
  have hbas : basis (Fin.last n) (Fin.last n)=1 := by simp [basis]
  rw [hbas,mul_one]
  have h0 := mul_nonpos_of_nonneg_of_nonpos hw
    (chain_gradient_nonpos n ℓ h hℓ hh z (Fin.last n))
  have hq := releaseCoefficient_nonpos b r (z (Fin.last n)) hb hr
  linarith

theorem microLatent_norm_bound (Cg J : ℝ) (n : ℕ) (ℓ h A ν g b w r : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) (hb : 0<b) (hw : 0≤w)
    (hchain : ∀ z : Space n, ‖gradient (chain n ℓ h) z‖≤Cg*(ℓ*h)*Real.sqrt ((n:ℝ)+1))
    (hJ : ∀ t,|deriv releaseGate t|≤J) (z : Space n) :
    ‖gradient (microLatent n ℓ h A ν g b w r) z‖≤
      w*(Cg*(ℓ*h)*Real.sqrt ((n:ℝ)+1)+A*(3*ν*b+g))+|r| *J/b := by
  rw [microLatent_gradient]
  have hbas : ‖basis (Fin.last n)‖=1 := by simp [basis,EuclideanSpace.norm_single]
  have hc : ‖w • gradient (chain n ℓ h) z‖≤w*(Cg*(ℓ*h)*Real.sqrt ((n:ℝ)+1)) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (hchain z) hw
  have hs := positiveReceiverSlope_abs_bound A ν g h b (z (Fin.last n)) hA hν hg hh hb
  have hq := releaseCoefficient_abs_bound b r (z (Fin.last n)) J hb (hJ _)
  have hterm : ‖(w*positiveReceiverSlope A ν g h b (z (Fin.last n))+
      releaseCoefficient b r (z (Fin.last n))) • basis (Fin.last n)‖≤
      w*(A*(3*ν*b+g))+|r| *J/b := by
    rw [norm_smul,Real.norm_eq_abs,hbas,mul_one]
    have ht := abs_add (w*positiveReceiverSlope A ν g h b (z (Fin.last n)))
      (releaseCoefficient b r (z (Fin.last n)))
    rw [abs_mul,abs_of_nonneg hw] at ht
    exact ht.trans (add_le_add (mul_le_mul_of_nonneg_left hs hw) hq)
  have ht := (norm_add_le _ _).trans (add_le_add hc hterm)
  nlinarith only [ht]

/-- First-small-coordinate margin for the exact one-sided micro chain. -/
theorem micro_interior_small_margin (n : ℕ) (ℓ h A ν g b w r c q : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0≤ν) (hg : g=ℓ*h)
    (hh : 0<h) (hb : 0<b) (hw : 0≤w) (hr : r≤0)
    (hc : 0≤c) (hq : 2/3≤q) (hwidth : c*h≤w*g/6)
    (z : Space n) (hz : z (Fin.last n)<h) :
    w*g/2≤‖c • z+q • gradient (microLatent n ℓ h A ν g b w r) z‖ := by
  obtain ⟨j,hj,hgrad⟩ := chain_frontier n ℓ h hℓ hh z hz
  have hp := (microLatent_coord_le_chain n ℓ h A ν g b w r hA hν
    (by rw [hg];positivity) hh hb hw hr z j).trans (mul_le_mul_of_nonneg_left hgrad hw)
  rw [←hg] at hp
  have hp0 := microLatent_nonpos n ℓ h A ν g b w r hℓ hA hν
    (by rw [hg];positivity) hh hb hw hr z j
  have hrad := mul_le_mul_of_nonneg_left hj.le hc
  have hqg := mul_le_mul_of_nonpos_right hq hp0
  apply negative_coordinate_norm_margin _ j
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  nlinarith

/-- The positive terminal receiver covers the remaining terminal positions
before release. Only proved coordinate derivatives are used. -/
theorem micro_interior_margin (n : ℕ) (ℓ h A ν g b w r wstar c q : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0≤ν) (hg : g=ℓ*h)
    (hh : 0<h) (hb : 0<b) (hws : 0≤wstar) (hw : wstar≤w) (hr : r≤0)
    (hc : 0≤c) (hcup : c≤5*ν/4) (hq : 2/3≤q)
    (hwidth : c*h≤wstar*g/6) (hAw : 8≤w*A)
    (z : Space n) (hQ : releaseGate (z (Fin.last n)/b)<1) :
    min wstar 1*g/2≤‖c • z+q • gradient (microLatent n ℓ h A ν g b w r) z‖ := by
  have hg0 : 0≤g := by rw [hg];positivity
  have hw0 : 0≤w := hws.trans hw
  by_cases hz : z (Fin.last n)<h
  · have hwidthw : c*h≤w*g/6 := hwidth.trans (by nlinarith [mul_le_mul_of_nonneg_right hw hg0])
    have hm : min wstar 1*g/2≤w*g/2 := by
      nlinarith [mul_le_mul_of_nonneg_right ((min_le_left wstar 1).trans hw) hg0]
    exact hm.trans (micro_interior_small_margin n ℓ h A ν g b w r c q
      hℓ hA hν hg hh hb hw0 hr hc hq hwidthw z hz)
  let t := z (Fin.last n)
  let p := gradient (microLatent n ℓ h A ν g b w r) z (Fin.last n)
  have ht : h≤t := le_of_not_gt hz
  have ht0 : 0≤t := hh.le.trans ht
  have htupper : t<2*b := by
    by_contra hu
    have he : releaseGate (t/b)=1 := releaseGate_one ((le_div_iff₀ hb).mpr (le_of_not_gt hu))
    change releaseGate (t/b)<1 at hQ
    rw [he] at hQ
    exact lt_irrefl _ hQ
  have hact := positiveReceiverSlope_active A ν g h b t hh hb (by linarith) htupper.le
  have hpbound := microLatent_terminal_le_receiver n ℓ h A ν g b w r hℓ hh hb hw0 hr z
  change p≤w*positiveReceiverSlope A ν g h b t at hpbound
  rw [hact] at hpbound
  have harg : 0≤ν*t+g := by positivity
  have hp8 : p≤-8*(ν*t+g) := by
    nlinarith only [hpbound,mul_le_mul_of_nonneg_right hAw harg]
  have hp0 := microLatent_nonpos n ℓ h A ν g b w r hℓ hA hν hg0 hh hb hw0 hr z (Fin.last n)
  change p≤0 at hp0
  have hqg := mul_le_mul_of_nonpos_right hq hp0
  have hrad := mul_le_mul_of_nonneg_right hcup ht0
  have hm := mul_le_mul_of_nonneg_right (min_le_right wstar 1) hg0
  apply negative_coordinate_norm_margin _ (Fin.last n)
  change c*t+q*p≤-(min wstar 1*g/2)
  nlinarith only [hp8,hqg,hrad,hm,mul_nonneg hν ht0,hg0]

/-- The actual norm budget simplifies to a fixed multiple of L*b under
source-scale inequalities. No gradient-size certificate is postulated. -/
theorem microLatent_norm_calibrated (Cg J Cr : ℝ) (hCg : 0≤Cg) (hJ : 0≤J) (_hCr : 0≤Cr)
    (hchain : ∀ (n : ℕ) (ℓ h : ℝ),0≤ℓ → 0<h → ∀ z : Space n,
      ‖gradient (chain n ℓ h) z‖≤Cg*(ℓ*h)*Real.sqrt ((n:ℝ)+1))
    (hgate : ∀ t,|deriv releaseGate t|≤J)
    (n : ℕ) (ℓ b κ ζ A w r : ℝ) (hℓ : 0≤ℓ) (hb : 0<b) (hκ : 1≤κ)
    (hζ : 0≤ζ) (hζ1 : ζ≤1) (hA : 0≤A) (hw : 0≤w) (hwe : w≤Real.exp 1)
    (hr : |r|≤Cr*ℓ*b^2) (hsize : Real.sqrt ((n:ℝ)+1)≤κ) (z : Space n) :
    ‖gradient (microLatent n ℓ (b/κ) A (ζ*ℓ) (ℓ*(b/κ)) b w r) z‖≤
      (Real.exp 1*(Cg+4*A)+Cr*J)*(ℓ*b) := by
  have hκ0 : 0<κ := by linarith
  have hh : 0<b/κ := div_pos hb hκ0
  have hhupper : b/κ≤b := div_le_self hb.le hκ
  have hscaled : (b/κ)*Real.sqrt ((n:ℝ)+1)≤b := by
    have ht := mul_le_mul_of_nonneg_left hsize hh.le
    simpa only [div_mul_cancel₀ _ hκ0.ne'] using ht
  have hchainpart : Cg*(ℓ*(b/κ))*Real.sqrt ((n:ℝ)+1)≤Cg*(ℓ*b) := by
    have ht := mul_le_mul_of_nonneg_left hscaled (mul_nonneg hCg hℓ)
    nlinarith only [ht]
  have hν : ζ*ℓ≤ℓ := by nlinarith [mul_le_mul_of_nonneg_right hζ1 hℓ]
  have hg : ℓ*(b/κ)≤ℓ*b := mul_le_mul_of_nonneg_left hhupper hℓ
  have hrecv : A*(3*(ζ*ℓ)*b+ℓ*(b/κ))≤4*A*(ℓ*b) := by
    have ht := mul_le_mul_of_nonneg_right hν hb.le
    nlinarith [mul_le_mul_of_nonneg_left (show 3*(ζ*ℓ)*b+ℓ*(b/κ)≤4*(ℓ*b) by linarith) hA]
  have hinside : Cg*(ℓ*(b/κ))*Real.sqrt ((n:ℝ)+1)+A*(3*(ζ*ℓ)*b+ℓ*(b/κ))≤
      (Cg+4*A)*(ℓ*b) := by nlinarith only [hchainpart,hrecv]
  have hwpart : w*(Cg*(ℓ*(b/κ))*Real.sqrt ((n:ℝ)+1)+A*(3*(ζ*ℓ)*b+ℓ*(b/κ)))≤
      Real.exp 1*((Cg+4*A)*(ℓ*b)) :=
    (mul_le_mul_of_nonneg_left hinside hw).trans
      (mul_le_mul_of_nonneg_right hwe (by positivity))
  have hrpart : |r| *J/b≤(Cr*J)*(ℓ*b) := by
    calc
      _≤(Cr*ℓ*b^2)*J/b := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hr hJ) hb.le
      _=(Cr*J)*(ℓ*b) := by field_simp;ring
  have hnorm := microLatent_norm_bound Cg J n ℓ (b/κ) A (ζ*ℓ) (ℓ*(b/κ)) b w r
    hA (mul_nonneg hζ hℓ) (mul_nonneg hℓ hh.le) hh hb hw (hchain n ℓ (b/κ) hℓ hh) hgate z
  nlinarith only [hnorm,hwpart,hrpart]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def microAttached (n : ℕ) (ℓ h A ν g b w r R : ℝ) (V : Space n →ₗᵢ[ℝ] E) : E → ℝ :=
  wrapped ν R (microLatent n ℓ h A ν g b w r) V.toContinuousLinearMap.adjoint

theorem microAttached_formula (n : ℕ) (ℓ h A ν g b w r R : ℝ)
    (V : Space n →ₗᵢ[ℝ] E) (u : E) :
    microAttached n ℓ h A ν g b w r R V u=
      bowl ν R u+w*(chain n ℓ h (WrappedChain.coordinates n R V u)+
        positiveReceiver A ν g h b (WrappedChain.coordinates n R V u (Fin.last n)))+
      r*releaseGate (WrappedChain.coordinates n R V u (Fin.last n)/b) := by
  simp only [microAttached,wrapped,microLatent,WrappedChain.coordinates]
  ring

theorem microAttached_hasGradientAt (n : ℕ) (ℓ h A ν g b w r R : ℝ) (hR : 0<R)
    (V : Space n →ₗᵢ[ℝ] E) (u : E) :
    HasGradientAt (microAttached n ℓ h A ν g b w r R V)
      (wrappedGradient ν R u (V (gradient (microLatent n ℓ h A ν g b w r)
        (WrappedChain.coordinates n R V u)))) u := by
  have hd := wrapped_hasGradientAt ν R hR (microLatent n ℓ h A ν g b w r)
    V.toContinuousLinearMap.adjoint u _
    (microLatent_hasGradientAt n ℓ h A ν g b w r (WrappedChain.coordinates n R V u)).differentiableAt.hasGradientAt
  simpa only [microAttached,ContinuousLinearMap.adjoint_adjoint,
    LinearIsometry.coe_toContinuousLinearMap] using hd

/-- Analytic assembly under explicit scalar budgets. The uniform micro
parameter theorem below discharges these budgets for the actual gradients. -/
theorem microAttached_margin_from_budgets (n : ℕ) (ℓ h A ν g b w r wstar R G : ℝ)
    (hℓ : 0≤ℓ) (hA : 0≤A) (hν : 0≤ν) (hg : g=ℓ*h)
    (hh : 0<h) (hb : 0<b) (hws : 0≤wstar) (hw : wstar≤w) (hr : r≤0)
    (hR : 0<R) (hG : 0≤G)
    (hactual : ∀ z : Space n,‖gradient (microLatent n ℓ h A ν g b w r) z‖≤G)
    (hbudget : 4*G≤ν*R) (hwidth : (5*ν/4)*h≤wstar*g/6)
    (hAw : 8≤w*A) (hexterior : min wstar 1*g/2≤2*ν*R/3-G)
    (V : Space n →ₗᵢ[ℝ] E) (u : E)
    (hQ : releaseGate (WrappedChain.coordinates n R V u (Fin.last n)/b)<1) :
    min wstar 1*g/2≤‖gradient (microAttached n ℓ h A ν g b w r R V) u‖ := by
  let z := WrappedChain.coordinates n R V u
  let p := gradient (microLatent n ℓ h A ν g b w r) z
  have hp : ‖p‖≤G := hactual z
  rw [(microAttached_hasGradientAt n ℓ h A ν g b w r R hR V u).gradient]
  change min wstar 1*g/2≤‖wrappedGradient ν R u (V p)‖
  rcases le_total ‖u‖ R with hu|hu
  · have hz : ‖z‖≤R := (frame_adjoint_norm_le V _).trans (compress_norm_le_radius R hR u)
    have hi : ⟪z,p⟫≤R*G := (real_inner_le_norm z p).trans
      (mul_le_mul hz hp (norm_nonneg _) hR.le)
    have hDbudget : 2*(R*G)≤ν*R^2 := by
      have hb := mul_le_mul_of_nonneg_right hbudget hR.le
      nlinarith
    obtain ⟨hcl,hcu⟩ := radialCoefficient_bounds_from_budgets ν R G (R*G)
      hR hG (mul_nonneg hR.le hG) V u p hp hi hDbudget hbudget
    have hc0 : 0≤radialCoefficient ν R V u p := (by positivity : 0≤ν/2).trans hcl
    have hcw : radialCoefficient ν R V u p*h≤wstar*g/6 :=
      (mul_le_mul_of_nonneg_right hcu hh.le).trans hwidth
    have hm := micro_interior_margin n ℓ h A ν g b w r wstar
      (radialCoefficient ν R V u p) (scale R u) hℓ hA hν hg hh hb hws hw hr hc0 hcu
      (scale_interior_lower R hR u hu) hcw hAw z hQ
    have he := projected_wrappedGradient ν R V u p
    change V.toContinuousLinearMap.adjoint (wrappedGradient ν R u (V p))=
      radialCoefficient ν R V u p • z+scale R u • p at he
    change min wstar 1*g/2≤‖radialCoefficient ν R V u p • z+scale R u • p‖ at hm
    rw [←he] at hm
    exact hm.trans (frame_adjoint_norm_le V _)
  · have ht := exterior_endgame ν R G (min wstar 1*g) hν hR hG hexterior u (V p) hu
      (by simpa using hp)
    exact ht

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Numerical source-scale micro certificate. The norm and radial hypotheses
of the assembly theorem are derived from the literal chain and receivers. -/
theorem numerical_micro_endgame (Cr wstar : ℝ) (hCr : 0≤Cr) (hws : 0<wstar) :
    ∃ A Cu ζ κ₀ : ℝ,0<A ∧ 0<Cu ∧ 0<ζ ∧ ζ≤1 ∧ 4≤κ₀ ∧
      2/ζ^3≤κ₀ ∧
    ∀ (n : ℕ) (ℓ b κ w r : ℝ),0<ℓ → 0<b → κ₀≤κ →
      Real.sqrt ((n:ℝ)+1)≤κ → wstar≤w → w≤Real.exp 1 → r≤0 → |r|≤Cr*ℓ*b^2 →
      ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
        (V : Space n →ₗᵢ[ℝ] F) (u : F),
        releaseGate (WrappedChain.coordinates n (Cu*b/ζ) V u (Fin.last n)/b)<1 →
        min wstar 1*(ℓ*(b/κ))/2≤
          ‖gradient (microAttached n ℓ (b/κ) A (ζ*ℓ) (ℓ*(b/κ)) b w r (Cu*b/ζ) V) u‖ := by
  obtain ⟨Cg,hCg,hchain⟩ := chain_gradient_norm_uniform
  obtain ⟨J,hJ,hgate⟩ := releaseGate_deriv_bound
  let A := 1+8/wstar
  have hA : 0<A := by dsimp [A];positivity
  let C := Real.exp 1*(Cg+4*A)+Cr*J
  have hC : 0≤C := by dsimp [C];positivity
  let Cu := 8*(C+1)
  have hCu : 0<Cu := by dsimp [Cu];positivity
  let ζ := min (1/8) (wstar/20)
  have hζ : 0<ζ := lt_min (by norm_num) (by positivity)
  have hζ1 : ζ≤1 := (min_le_left _ _).trans (by norm_num)
  have hζw : ζ≤wstar/20 := min_le_right _ _
  let κ₀ := max 4 (2/ζ^3)
  refine ⟨A,Cu,ζ,κ₀,hA,hCu,hζ,hζ1,le_max_left _ _,le_max_right _ _,?_⟩
  intro n ℓ b κ w r hℓ hb hκ hsize hw hwe hr hrbound F _ _ _ V u hQ
  have hκ1 : 1≤κ := (by norm_num : (1:ℝ)≤4).trans ((le_max_left _ _).trans hκ)
  have hκ0 : 0<κ := by linarith
  have hh : 0<b/κ := div_pos hb hκ0
  have hg0 : 0≤ℓ*(b/κ) := mul_nonneg hℓ.le hh.le
  have hR : 0<Cu*b/ζ := div_pos (mul_pos hCu hb) hζ
  have hν0 : 0≤ζ*ℓ := mul_nonneg hζ.le hℓ.le
  have hw0 : 0≤w := hws.le.trans hw
  have hscale : (ζ*ℓ)*(Cu*b/ζ)=Cu*(ℓ*b) := by field_simp;ring
  have hG : 0≤C*(ℓ*b) := mul_nonneg hC (mul_nonneg hℓ.le hb.le)
  have hbudget : 4*(C*(ℓ*b))≤(ζ*ℓ)*(Cu*b/ζ) := by
    rw [hscale]
    dsimp [Cu]
    nlinarith [mul_nonneg hC (mul_nonneg hℓ.le hb.le)]
  have hwidth : (5*(ζ*ℓ)/4)*(b/κ)≤wstar*(ℓ*(b/κ))/6 := by
    have ht : 5*ζ/4≤wstar/6 := by linarith only [hζw,hws]
    have hm := mul_le_mul_of_nonneg_right ht hg0
    nlinarith only [hm]
  have hAwstar : wstar*A=wstar+8 := by dsimp [A];field_simp
  have hAw : 8≤w*A := by
    have ht := mul_le_mul_of_nonneg_right hw hA.le
    nlinarith only [ht,hAwstar,hws]
  have hexterior : min wstar 1*(ℓ*(b/κ))/2≤2*(ζ*ℓ)*(Cu*b/ζ)/3-C*(ℓ*b) := by
    have hhupper : b/κ≤b := div_le_self hb.le hκ1
    have hgup := mul_le_mul_of_nonneg_left hhupper hℓ.le
    have hm := mul_le_mul_of_nonneg_right (min_le_right wstar 1) hg0
    have hex : ℓ*b≤2*(ζ*ℓ)*(Cu*b/ζ)/3-C*(ℓ*b) := by
      have hs : 2*(ζ*ℓ)*(Cu*b/ζ)/3=2*(Cu*(ℓ*b))/3 := by rw [mul_assoc,hscale]
      rw [hs]
      dsimp only [Cu]
      apply sub_nonneg.mp
      convert mul_nonneg (by norm_num : (0:ℝ)≤13/3)
        (mul_nonneg (add_nonneg hC zero_le_one) (mul_nonneg hℓ.le hb.le)) using 1; ring
    nlinarith only [hm,hgup,hg0,hex]
  apply microAttached_margin_from_budgets n ℓ (b/κ) A (ζ*ℓ) (ℓ*(b/κ)) b w r wstar
    (Cu*b/ζ) (C*(ℓ*b)) hℓ.le hA.le hν0 rfl hh hb hws.le hw hr hR hG _ hbudget hwidth hAw hexterior V u hQ
  intro z
  exact microLatent_norm_calibrated Cg J Cr hCg hJ hCr hchain hgate n ℓ b κ ζ A w r
    hℓ.le hb hκ1 hζ.le hζ1 hA.le hw0 hwe hrbound hsize z

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The source's actual natural floor provides all required dimension and
chain-gradient geometry. No extra count premise is retained. -/
theorem micro_floor_geometry {ζ κ : ℝ} (hζ : 0<ζ) (hζ1 : ζ≤1)
    (hκ : 4≤κ) (hκscale : 2/ζ^3≤κ) :
    let M := Nat.floor (ζ^6*κ^2)
    1≤M ∧ Real.sqrt (((M-1:ℕ):ℝ)+1)≤κ := by
  let M := Nat.floor (ζ^6*κ^2)
  have hκ0 : 0<κ := by linarith
  have hscale : 2≤ζ^3*κ := by
    have ht := (div_le_iff₀ (pow_pos hζ 3)).mp hκscale
    nlinarith only [ht]
  have hy4 : 4≤ζ^6*κ^2 := by
    calc
      (4:ℝ)=2^2 := by norm_num
      _≤(ζ^3*κ)^2 := pow_le_pow_left₀ (by norm_num) hscale 2
      _=ζ^6*κ^2 := by ring
  have hM : 1≤M := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hf : (M:ℝ)≤ζ^6*κ^2 := Nat.floor_le (by positivity)
  have hz6 : ζ^6≤1 := pow_le_one₀ hζ.le hζ1
  have hbound : (M:ℝ)≤κ^2 := hf.trans (by
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hz6 (sq_nonneg κ)))
  refine ⟨hM,?_⟩
  apply (Real.sqrt_le_left hκ0.le).mpr
  have hn : ((M-1:ℕ):ℝ)+1=(M:ℝ) := by exact_mod_cast Nat.sub_add_cancel hM
  rw [hn]
  exact hbound

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Literal common-wrapper micro certificate with the source's actual
M=floor(zeta^6*kappa^2), beta=b/kappa and fixed numerical parameter choices.
The only size input about the macro residual is its displayed scalar
|R_i|<=Cr*L*b^2 bound; all latent norm, receiver and radial budgets are proved. -/
theorem literal_micro_certificate (Cr wstar : ℝ) (hCr : 0≤Cr) (hws : 0<wstar) :
    ∃ A Cu ζ κ₀ cu : ℝ,0<A ∧ 0<Cu ∧ 0<ζ ∧ ζ≤1 ∧ 4≤κ₀ ∧ 0<cu ∧
    ∀ (ℓ b κ w r : ℝ),0<ℓ → 0<b → κ₀≤κ → wstar≤w → w≤Real.exp 1 →
      r≤0 → |r|≤Cr*ℓ*b^2 →
      let M := Nat.floor (ζ^6*κ^2)
      1≤M ∧ ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
        (V : Space (M-1) →ₗᵢ[ℝ] F) (u : F),
        releaseGate (WrappedChain.coordinates (M-1) (Cu*b/ζ) V u (Fin.last (M-1))/b)<1 →
        cu*(ℓ*(b/κ))≤
          ‖gradient (microAttached (M-1) ℓ (b/κ) A (ζ*ℓ) (ℓ*(b/κ)) b w r (Cu*b/ζ) V) u‖ := by
  obtain ⟨A,Cu,ζ,κ₀,hA,hCu,hζ,hζ1,hκ₀,hκscale,hcert⟩ := numerical_micro_endgame Cr wstar hCr hws
  let cu := min wstar 1/2
  have hcu : 0<cu := div_pos (lt_min hws zero_lt_one) (by norm_num)
  refine ⟨A,Cu,ζ,κ₀,cu,hA,hCu,hζ,hζ1,hκ₀,hcu,?_⟩
  intro ℓ b κ w r hℓ hb hκ hw hwe hr hrbound
  let M := Nat.floor (ζ^6*κ^2)
  have hgeom := micro_floor_geometry hζ hζ1 (hκ₀.trans hκ) (hκscale.trans hκ)
  refine ⟨hgeom.1,?_⟩
  intro F _ _ _ V u hQ
  have ht := hcert (M-1) ℓ b κ w r hℓ hb hκ hgeom.2 hw hwe hr hrbound F V u hQ
  change (min wstar 1/2)*(ℓ*(b/κ))≤_
  simpa only [div_mul_eq_mul_div] using ht

end Bilevel.PolishedLiteral
