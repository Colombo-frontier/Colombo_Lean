import Bilevel.PolishedBlockProjection

/-! Source-style local/global maximum bookkeeping. These are deterministic
geometry and arithmetic steps of `dt:lem:bookkeeping`, independent of a
probabilistic observer event. -/
noncomputable section
namespace Bilevel.PolishedObserverMaximum
open PolishedBlockProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Simultaneously initializing a local or global space with a block of
newly named columns costs one factor two, independent of the block size. -/
theorem initialize_named_block (W : Submodule ℝ E) (C : ι → E) (F : κ → E)
    (hC : Orthonormal ℝ C) (hF : Orthonormal ℝ F)
    (hCF : ∀ j i,inner (𝕜:=ℝ) (C j) (F i)=0) {z : ℝ}
    (hz : 0≤z) (hzsmall : z≤1/2)
    (hsource : blockEnergy W C≤z) (htarget : blockEnergy W F≤z) :
    blockEnergy (W ⊔ columnSpace C) F≤2*z := by
  have he : blockEnergy W C<1 := by linarith
  have h := disclosing_orthogonal_named_columns W C F hC hF hCF he
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0<1-blockEnergy W C)).mpr
  have hn := mul_nonneg hz (show 0≤z-blockEnergy W C by linarith)
  have hs := mul_nonneg hz (show 0≤1-2*z by linarith)
  nlinarith

/-- Each of the four actual local/global energy formulas in the source
is at most seventeen times the current common maximum. -/
theorem directed_action_bound {a b g localNew globalNew z : ℝ}
    (ha : a≤z) (hb : b≤z) (hg : g≤z)
    (hlocal : localNew≤9*b+8*a) (hglobal : globalNew≤9*g+8*a) :
    localNew≤17*z ∧ globalNew≤17*z := by
  constructor <;> linarith

/-- In particular the already-controlled post-forward local energy can
be used for the reverse source; its bound is derived, not assumed. -/
theorem forward_reverse_bound {a b gL gR b1 a1 outL outR z : ℝ}
    (hz : 0≤z) (ha : a≤z) (hb : b≤z) (hgL : gL≤z) (hgR : gR≤z)
    (hb1 : b1≤9*b+8*a) (hR : outR≤9*gR+8*a)
    (ha1 : a1≤9*a+8*b1) (hL : outL≤9*gL+8*b1) :
    b1≤17*z ∧ outR≤17*z ∧ a1≤17*(17*z) ∧ outL≤17*(17*z) := by
  obtain ⟨hb',hR'⟩ := directed_action_bound ha hb hgR hb1 hR
  have ha' : a≤17*z := ha.trans (by linarith)
  have hL' : gL≤17*z := hgL.trans (by linarith)
  obtain ⟨ha'',hL''⟩ := directed_action_bound hb' ha' hL' ha1 hL
  exact ⟨hb',hR',ha'',hL''⟩

/- Source and paired-domain inclusions after the forward action. These
are exactly A1=A0+S and B1=O A1 inside the newly enlarged local spaces. -/
omit [FiniteDimensional ℝ E] in
theorem forward_paired_inclusions (O : E →ₗ[ℝ] E)
    (A₀ S Lsrc Ldst : Submodule ℝ E)
    (hA : A₀≤Lsrc) (hS : S≤Lsrc) (hB : A₀.map O≤Ldst) :
    A₀ ⊔ S≤Lsrc ∧ (A₀ ⊔ S).map O≤Ldst ⊔ S.map O := by
  constructor
  · exact sup_le hA hS
  · rw [Submodule.map_sup]
    exact sup_le (hB.trans le_sup_left) le_sup_right

omit [FiniteDimensional ℝ E] in
theorem reverse_paired_inclusions (O : E ≃ₗ[ℝ] E)
    (A₁ Sdst Lsrc Ldst : Submodule ℝ E)
    (hA : A₁≤Lsrc) (hB : A₁.map O.toLinearMap≤Ldst) (hS : Sdst≤Ldst) :
    A₁⊔Sdst.map O.symm.toLinearMap≤Lsrc⊔Sdst.map O.symm.toLinearMap ∧
    (A₁⊔Sdst.map O.symm.toLinearMap).map O.toLinearMap=A₁.map O.toLinearMap⊔Sdst ∧
    (A₁⊔Sdst.map O.symm.toLinearMap).map O.toLinearMap≤Ldst := by
  have he : (Sdst.map O.symm.toLinearMap).map O.toLinearMap=Sdst := by
    ext y
    constructor
    · rintro ⟨x,⟨v,hv,rfl⟩,rfl⟩
      simpa only [LinearEquiv.coe_coe,O.apply_symm_apply] using hv
    · intro hy
      exact ⟨O.symm y,⟨y,hy,rfl⟩,O.apply_symm_apply y⟩
  refine ⟨sup_le (hA.trans le_sup_left) le_sup_right,?_,?_⟩
  · rw [Submodule.map_sup,he]
  · rw [Submodule.map_sup,he]
    exact sup_le hB hS

end Bilevel.PolishedObserverMaximum
