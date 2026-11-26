import Bilevel.ChiOuterCarrierTransfer

/-! The source r_j ledger including the actual one-sided outer selection.
All outer and inner selector jets and mixed derivatives are constructed. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerCarrier (m : ℕ) (M : Node E) (D : Geometry F) (d t : ℕ) : Joint E (Blocks m F) → ℝ :=
  outerSelected m M (fun i => jointCarrier m D d 0 [i.val] t)

theorem outerCarrier_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (d t : ℕ) :
    ContDiff ℝ 3 (outerCarrier m M D d t) :=
  outerSelected_contDiff m M _ (fun i => jointCarrier_contDiff m D d 0 [i.val] t 3)

omit [CompleteSpace E] in
theorem sourceMacro_radius_ge_width {n : ℕ} {initial : Scale} {Km : ℝ}
    (hh : 0 < initial.width) (hKm : 1≤Km) (U : Space n →ₗᵢ[ℝ] E) :
    (sourceMacroNode n initial Km U).width≤(sourceMacroNode n initial Km U).radius := by
  have hn : (1:ℝ)≤(n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) n;linarith
  have hs : 1≤Real.sqrt ((n:ℝ)+1) := Real.one_le_sqrt.mpr hn
  change initial.width≤Km*initial.width*Real.sqrt ((n:ℝ)+1)
  have h₁ := mul_le_mul_of_nonneg_right hKm hh.le
  have h₂ := mul_le_mul_of_nonneg_left hs (show 0≤Km*initial.width by positivity)
  nlinarith only [h₁,h₂]

theorem source_outer_selected_ledger (A K ζ cn : ℝ) (hA : 0≤A) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) :
    ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (CR Km : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,128≤cn/(η j)^2) → (∀ j,0<b j) → (∀ j,b j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      ∀ (d t m : ℕ) (z : Joint E (Blocks m F)) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (outerCarrier m M D d t) z‖≤
        C^(t+2)*ledgerScale (((D t []).n:ℝ)+1) (D t []).ell (D t []).width q := by
  obtain ⟨Ci,hCi,hinner⟩ := source_selected_joint_ledger A K ζ cn hA hK hζ hζ1 hcn hcn1
  obtain ⟨Co,hCo,houter⟩ := constructed_outer_carrier_step
  let C := Ci+Co
  have hC : 1≤C := by unfold C;linarith
  have hCi0 : 0≤Ci := by linarith
  have hCo0 : 0≤Co := by linarith
  have hC0 : 0≤C := by linarith
  have hCiC : Ci≤C := by unfold C;linarith
  have hCoC : Co≤C := by unfold C;linarith
  refine ⟨C,hC,fun E F _ _ _ _ _ _ n initial hl hw r η b CR Km hr hη hη1 hlen hb hb1 hCR hCRcn hKm U V => ?_⟩
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  have hledger := hinner F initial hl hw r η b CR hr hη hη1 hlen hb hb1 hCR hCRcn V
  have hp := parentScale_positive initial r η hl hw hr hη
  have hmono := parentScale_width_antitone initial r η hl hw hr hη hη1
  intro d t m z q hq
  have hell : 0≤(D t []).ell := (hp (t+1)).1.le
  have hh : 0<(D t []).width := (hp (t+1)).2
  have hN : 1≤((D t []).n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) (D t []).n;linarith
  have hwidth : (D t []).width*Real.sqrt (((D t []).n:ℝ)+1)≤M.width :=
    (source_width_sqrt_length_le_parent hcn hcn1 (hη t) (hp t).2 (hr t) (hlen t)).trans
      (hmono (Nat.zero_le t))
  have hs := houter E F m M hw (sourceMacro_radius_ge_width hw hKm U)
    (fun i => jointCarrier m D d 0 [i.val] t)
    (fun i => jointCarrier_contDiff m D d 0 [i.val] t 3)
    (Ci^(t+1)) (((D t []).n:ℝ)+1) (D t []).ell (D t []).width (by positivity) hN hell hh hwidth z q hq
    (fun i k hk => by simpa only [Nat.zero_add] using hledger d 0 t [i.val] m z.snd k (by omega))
  have hcoeff : Co*Ci^(t+1)≤C^(t+2) := by
    calc
      _ ≤ C*C^(t+1) := mul_le_mul hCoC (pow_le_pow_left₀ hCi0 hCiC _) (by positivity) hC0
      _ = _ := by rw [show t+2=(t+1)+1 by omega,pow_succ];ring
  exact hs.trans (mul_le_mul_of_nonneg_right hcoeff
    (ledgerScale_nonneg (by positivity) hell hh.le q))

end Bilevel.ChiOuter
