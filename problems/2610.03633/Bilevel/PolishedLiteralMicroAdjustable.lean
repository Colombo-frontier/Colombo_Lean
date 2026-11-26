import Bilevel.PolishedLiteralMicro

/-! The common-wrapper constants are chosen before the small zeta, as in
the manuscript. Zeta may subsequently be shrunk to pay the macro value
budget without invalidating the already proved micro margin. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.PolishedLiteral
open ChiBoundedChain RadialWrapper ZeroChainPotential

/-- A and Cu are fixed before zeta; every sufficiently small positive zeta
admits a source condition-number threshold. -/
theorem parametric_micro_endgame_with_radius (Cr wstar : ℝ) (hCr : 0≤Cr) (hws : 0<wstar) :
    ∃ A Cu : ℝ,0<A ∧ 1≤Cu ∧
    ∀ ζ : ℝ,0<ζ → ζ≤1 → ζ≤wstar/20 →
    ∃ κ₀ : ℝ,4≤κ₀ ∧ 2/ζ^3≤κ₀ ∧
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
  have hCu1 : 1≤Cu := by dsimp [Cu];linarith only [hC]
  refine ⟨A,Cu,hA,hCu1,?_⟩
  intro ζ hζ hζ1 hζw
  let κ₀ := max 4 (2/ζ^3)
  refine ⟨κ₀,le_max_left _ _,le_max_right _ _,?_⟩
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

/-- Compatibility form with the original positive-radius interface. -/
theorem parametric_micro_endgame (Cr wstar : ℝ) (hCr : 0≤Cr) (hws : 0<wstar) :
    ∃ A Cu : ℝ,0<A ∧ 0<Cu ∧
    ∀ ζ : ℝ,0<ζ → ζ≤1 → ζ≤wstar/20 →
    ∃ κ₀ : ℝ,4≤κ₀ ∧ 2/ζ^3≤κ₀ ∧
    ∀ (n : ℕ) (ℓ b κ w r : ℝ),0<ℓ → 0<b → κ₀≤κ →
      Real.sqrt ((n:ℝ)+1)≤κ → wstar≤w → w≤Real.exp 1 → r≤0 → |r|≤Cr*ℓ*b^2 →
      ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
        (V : Space n →ₗᵢ[ℝ] F) (u : F),
        releaseGate (WrappedChain.coordinates n (Cu*b/ζ) V u (Fin.last n)/b)<1 →
        min wstar 1*(ℓ*(b/κ))/2≤
          ‖gradient (microAttached n ℓ (b/κ) A (ζ*ℓ) (ℓ*(b/κ)) b w r (Cu*b/ζ) V) u‖ := by
  obtain ⟨A,Cu,hA,hCu,hcert⟩ := parametric_micro_endgame_with_radius Cr wstar hCr hws
  exact ⟨A,Cu,hA,lt_of_lt_of_le zero_lt_one hCu,hcert⟩

/-- Literal floor-calibrated micro certificate with the source quantifier
order A,Cu then arbitrarily small zeta then kappa0. All count/norm/radial
geometry is discharged from actual definitions. -/
theorem adjustable_literal_micro_certificate (Cr wstar : ℝ) (hCr : 0≤Cr) (hws : 0<wstar) :
    ∃ A Cu cu : ℝ,0<A ∧ 0<Cu ∧ 0<cu ∧
    ∀ ζ : ℝ,0<ζ → ζ≤1 → ζ≤wstar/20 →
    ∃ κ₀ : ℝ,4≤κ₀ ∧
    ∀ (ℓ b κ w r : ℝ),0<ℓ → 0<b → κ₀≤κ → wstar≤w → w≤Real.exp 1 →
      r≤0 → |r|≤Cr*ℓ*b^2 →
      let M := Nat.floor (ζ^6*κ^2)
      1≤M ∧ ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
        (V : Space (M-1) →ₗᵢ[ℝ] F) (u : F),
        releaseGate (WrappedChain.coordinates (M-1) (Cu*b/ζ) V u (Fin.last (M-1))/b)<1 →
        cu*(ℓ*(b/κ))≤
          ‖gradient (microAttached (M-1) ℓ (b/κ) A (ζ*ℓ) (ℓ*(b/κ)) b w r (Cu*b/ζ) V) u‖ := by
  obtain ⟨A,Cu,hA,hCu,hcert⟩ := parametric_micro_endgame Cr wstar hCr hws
  let cu := min wstar 1/2
  have hcu : 0<cu := div_pos (lt_min hws zero_lt_one) (by norm_num)
  refine ⟨A,Cu,cu,hA,hCu,hcu,?_⟩
  intro ζ hζ hζ1 hζw
  obtain ⟨κ₀,hκ₀,hκscale,hend⟩ := hcert ζ hζ hζ1 hζw
  refine ⟨κ₀,hκ₀,?_⟩
  intro ℓ b κ w r hℓ hb hκ hw hwe hr hrbound
  let M := Nat.floor (ζ^6*κ^2)
  have hgeom := micro_floor_geometry hζ hζ1 (hκ₀.trans hκ) (hκscale.trans hκ)
  refine ⟨hgeom.1,?_⟩
  intro F _ _ _ V u hQ
  have ht := hend (M-1) ℓ b κ w r hℓ hb hκ hgeom.2 hw hwe hr hrbound F V u hQ
  change (min wstar 1/2)*(ℓ*(b/κ))≤_
  simpa only [div_mul_eq_mul_div] using ht

end Bilevel.PolishedLiteral
