import Bilevel.ChiOuterCarrierLedger
import Bilevel.ChiCarrierFineSupport

/-! The complete outer-and-inner selected fine frontier and piece ledger.
The outer selector is the actual one-sided source macro selector. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainSchedule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerFineFrontier (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) : Joint E (Blocks m F) → ℝ :=
  outerSelected m M (fun i => selectedFineFrontier m D d 0 [i.val])

def outerFinePiece (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ) (p : ℕ) : Joint E (Blocks m F) → ℝ :=
  outerSelected m M (fun i => selectedFinePiece m D d 0 [i.val] c θ p)

theorem outerFineFrontier_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) :
    ContDiff ℝ 3 (outerFineFrontier m M D d) :=
  outerSelected_contDiff m M _ (fun i => selectedFineFrontier_contDiff m D d 0 [i.val])

theorem outerFinePiece_contDiff (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ) (p : ℕ) :
    ContDiff ℝ 3 (outerFinePiece m M D d c θ p) :=
  outerSelected_contDiff m M _ (fun i => selectedFinePiece_contDiff m D d 0 [i.val] c θ p)

theorem outerFinePiece_sum (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ) (c θ : ℝ)
    (z : Joint E (Blocks m F)) :
    (∑ p : Fin (levels θ+1),outerFinePiece m M D d c θ p.val z)=outerFineFrontier m M D d z := by
  unfold outerFinePiece outerFineFrontier outerSelected
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum,selectedFinePiece_sum]

theorem source_outer_selected_fine_ledger : ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (A K ζ cn CR Km : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,0<b j) → (∀ j,b j≤1) → 1≤K → 0<ζ → ζ≤1 → 1≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial r η b A K ζ cn CR V
      ∀ (d m : ℕ) (z : Joint E (Blocks m F)) (q : ℕ),q≤3 →
      let ℓ := (D d []).ell
      let β := (D d []).width
      (‖iteratedFDeriv ℝ q (outerFineFrontier m M D d) z‖≤
        C^(d+2)*fineScale (ℓ*β^2) (ℓ*β) β q) ∧
      (∀ (c θ : ℝ),0<c → c≤1/128 → 1≤θ → ∀ p,p≤levels θ →
        ‖iteratedFDeriv ℝ q (outerFinePiece m M D d c θ p) z‖≤
          C^(d+2)*fineScale ((ℓ*β^2)*θ^(-amplitudeExponent p)) (ℓ*β)
            (pieceResolution c β θ p) q) := by
  obtain ⟨Ci,hCi,hinner⟩ := source_selected_fine_ledger
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
  intro d m z q hq
  let ℓ := (D d []).ell
  let β := (D d []).width
  have hell : 0≤ℓ := (hp (d+1)).1.le
  have hβ : 0<β := (hp (d+1)).2
  have hβM : β≤M.width := hmono (Nat.zero_le (d+1))
  have hcoeff : Co*Ci^(d+1)≤C^(d+2) := by
    calc
      _ ≤ C*C^(d+1) := mul_le_mul hCoC (pow_le_pow_left₀ hCi0 hCiC _) (by positivity) hC0
      _ = _ := by rw [show d+2=(d+1)+1 by omega,pow_succ];ring
  have transport (f : Fin (M.n+1) → Blocks m F → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
      (a δ : ℝ) (ha : 0≤a) (hδ : 0<δ) (hδβ : δ≤β) (haβ : a≤(ℓ*β)*β)
      (hb : ∀ i k,k≤q → ‖iteratedFDeriv ℝ k (f i) z.snd‖≤Ci^(d+1)*fineScale a (ℓ*β) δ k) :
      ‖iteratedFDeriv ℝ q (outerSelected m M f) z‖≤C^(d+2)*fineScale a (ℓ*β) δ q := by
    have hs := houter E F m M hw (sourceMacro_radius_ge_width hw hKm U) f hf
      (Ci^(d+1)) a (ℓ*β) δ (by positivity) ha (by positivity) hδ (hδβ.trans hβM)
      (haβ.trans (mul_le_mul_of_nonneg_left hβM (by positivity))) z q hq hb
    exact hs.trans (mul_le_mul_of_nonneg_right hcoeff (fineScale_nonneg ha (by positivity) hδ.le q))
  constructor
  · exact transport _ (fun i => selectedFineFrontier_contDiff m D d 0 [i.val])
      (ℓ*β^2) β (by positivity) hβ le_rfl (by nlinarith)
      (fun i k hk => by simpa only [Nat.zero_add] using (hledger d 0 [i.val] m z.snd k (by omega)).1)
  · intro c θ hc hcs hθ p hpidx
    have hδ : 0<pieceResolution c β θ p := pieceResolution_pos c β θ hc hβ hθ p
    have hδβ : pieceResolution c β θ p≤β := (pieceResolution_le c β θ hc.le hβ.le hθ p hpidx).trans
      (mul_le_of_le_one_left hβ.le (show c≤1 by linarith))
    have hexp : 0≤amplitudeExponent p := by
      unfold amplitudeExponent
      split_ifs
      · norm_num
      · exact aExponent_nonneg _
    have hp1 := Real.rpow_le_one_of_one_le_of_nonpos hθ (neg_nonpos.mpr hexp)
    have haβ : (ℓ*β^2)*θ^(-amplitudeExponent p)≤(ℓ*β)*β := by
      have hs := mul_le_mul_of_nonneg_left hp1 (show 0≤ℓ*β^2 by positivity)
      nlinarith only [hs]
    exact transport _ (fun i => selectedFinePiece_contDiff m D d 0 [i.val] c θ p)
      ((ℓ*β^2)*θ^(-amplitudeExponent p)) (pieceResolution c β θ p) (by positivity) hδ hδβ haβ
      (fun i k hk => by simpa only [Nat.zero_add] using
        (hledger d 0 [i.val] m z.snd k (by omega)).2 c θ hc hcs hθ p hpidx)

end Bilevel.ChiOuter
