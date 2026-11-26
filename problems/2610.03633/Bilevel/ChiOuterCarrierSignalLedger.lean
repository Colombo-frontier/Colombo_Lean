import Bilevel.ChiOuterCarrierFineCoupling
import Bilevel.ChiCarrierSignalLedger

/-! The fixed inactive residual through all inner ancestors and the actual
one-sided outer selector. The resolution is fixed before the query point. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerFineFlatFrontier (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (τ : ℝ) : Joint E (Blocks m F) → ℝ :=
  outerSelected m M (fun i => selectedFineFlatFrontier m D d 0 [i.val] τ)

def outerFineSignal (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (τ : ℝ) : Joint E (Blocks m F) → ℝ :=
  outerSelected m M (fun i => selectedFineSignal m D d 0 [i.val] τ)

theorem outerFineSignal_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (τ : ℝ) :
    ContDiff ℝ 3 (outerFineSignal m M D d τ) :=
  outerSelected_contDiff m M _ (fun i => selectedFineSignal_contDiff m D d 0 [i.val] τ)

theorem outerFineSignal_eq_sub (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (τ : ℝ)
    (z : Joint E (Blocks m F)) :
    outerFineSignal m M D d τ z=outerFineFrontier m M D d z-outerFineFlatFrontier m M D d τ z := by
  simp only [outerFineSignal,outerFineFrontier,outerFineFlatFrontier,outerSelected,
    selectedFineSignal_eq_sub,mul_sub,Finset.sum_sub_distrib]

theorem source_outer_signal_ledger : ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (A K ζ cn CR Km : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,0<b j) → (∀ j,b j≤1) → 1≤K → 0<ζ → ζ≤1 → 1≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      ∀ (d m : ℕ) (τ : ℝ),0<τ → τ≤(D d []).width/16 →
      ∀ (z : Joint E (Blocks m F)) (q : ℕ),q≤3 →
      let ℓ := (D d []).ell
      let β := (D d []).width
      ‖iteratedFDeriv ℝ q (outerFineSignal m M D d τ) z‖≤
        C^(d+2)*fineScale ((ℓ*β)*τ) (ℓ*β) τ q := by
  obtain ⟨Ci,hCi,hinner⟩ := source_selected_signal_ledger
  obtain ⟨Co,hCo,houter⟩ := constructed_outer_fine_step
  let C := Ci+Co
  have hC : 1≤C := by unfold C;linarith
  have hCi0 : 0≤Ci := by linarith
  have hC0 : 0≤C := by linarith
  have hCiC : Ci≤C := by unfold C;linarith
  have hCoC : Co≤C := by unfold C;linarith
  refine ⟨C,hC,fun E F _ _ _ _ _ _ n initial hl hw r η b A K ζ cn CR Km hr hη hη1 hb hb1 hK hζ hζ1 hCR hKm U V => ?_⟩
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial r η b A K ζ cn CR V
  have hledger := hinner F initial hl hw r η b A K ζ cn CR hr hη hη1 hb hb1 hK hζ hζ1 hCR V
  have hp := parentScale_positive initial r η hl hw hr hη
  have hmono := parentScale_width_antitone initial r η hl hw hr hη hη1
  intro d m τ hτ hτβ z q hq
  let ℓ := (D d []).ell
  let β := (D d []).width
  have hell : 0≤ℓ := (hp (d+1)).1.le
  have hβ : 0<β := (hp (d+1)).2
  have hτβ' : τ≤β := by change τ≤β/16 at hτβ;linarith
  have hβM : β≤M.width := hmono (Nat.zero_le (d+1))
  have hcoeff : Co*Ci^(d+1)≤C^(d+2) := by
    calc
      _ ≤ C*C^(d+1) := mul_le_mul hCoC (pow_le_pow_left₀ hCi0 hCiC _) (by positivity) hC0
      _ = _ := by rw [show d+2=(d+1)+1 by omega,pow_succ];ring
  have hs := houter E F m M hw (sourceMacro_radius_ge_width hw hKm U)
    (fun i => selectedFineSignal m D d 0 [i.val] τ)
    (fun i => selectedFineSignal_contDiff m D d 0 [i.val] τ)
    (Ci^(d+1)) ((ℓ*β)*τ) (ℓ*β) τ (by positivity) (by positivity) (by positivity) hτ
    (hτβ'.trans hβM) (mul_le_mul_of_nonneg_left (hτβ'.trans hβM) (by positivity)) z q hq
    (by
      intro i k hk
      simpa only [Nat.zero_add] using hledger d 0 [i.val] m τ hτ
        (by simpa only [Nat.zero_add] using hτβ) z.snd k (by omega))
  exact hs.trans (mul_le_mul_of_nonneg_right hcoeff
    (fineScale_nonneg (by positivity) (by positivity) hτ.le q))

end Bilevel.ChiOuter
