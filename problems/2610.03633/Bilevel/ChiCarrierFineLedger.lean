import Bilevel.ChiCarrierFineLeaves
import Bilevel.ChiCarrierSourceWidths

/-! Actual ancestor-selected centered frontier and scheduled fine pieces.
Their joint bounds retain separate amplitude and positive-derivative scales. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive ZeroChainSchedule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def selectedFineFrontier (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) : Blocks m E → ℝ :=
  selectFamily m D (fun j I => jointFineFrontier m j (D j I)) d j I

def selectedFinePiece (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (c θ : ℝ) (p : ℕ) : Blocks m E → ℝ :=
  selectFamily m D (fun j I => jointFinePiece m j (D j I) c θ p) d j I

theorem selectedFineFrontier_contDiff (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) :
    ContDiff ℝ 3 (selectedFineFrontier m D d j I) :=
  selectFamily_contDiff m D _ (fun j I => jointFineFrontier_contDiff m j (D j I)) d j I

theorem selectedFinePiece_contDiff (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (c θ : ℝ) (p : ℕ) :
    ContDiff ℝ 3 (selectedFinePiece m D d j I c θ p) :=
  selectFamily_contDiff m D _ (fun j I => jointFinePiece_contDiff m j (D j I) c θ p) d j I

theorem selectedFinePiece_sum (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (c θ : ℝ) (x : Blocks m E) :
    (∑ p : Fin (levels θ+1),selectedFinePiece m D d j I c θ p.val x)=selectedFineFrontier m D d j I x := by
  have he : (fun j I x => ∑ p : Fin (levels θ+1),jointFinePiece m j (D j I) c θ p.val x)=
      (fun j I => jointFineFrontier m j (D j I)) := by
    funext j I x
    exact jointFinePiece_sum m j (D j I) c θ x
  unfold selectedFinePiece selectedFineFrontier
  rw [← selectFamily_sum m D (fun p : Fin (levels θ+1) => fun j I => jointFinePiece m j (D j I) c θ p.val),he]

/-- All frontier/piece jets are constructed, including mixed ancestor
derivatives. The common constant precedes every geometry, dimension and depth. -/
theorem source_selected_fine_ledger : ∃ C : ℝ,1≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (A K ζ cn CR : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,0<b j) → (∀ j,b j≤1) → 1≤K → 0<ζ → ζ≤1 → 1≤CR →
      ∀ (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let D := sourceGeometry initial r η b A K ζ cn CR U
      ∀ (d j : ℕ) (I : List ℕ) (m : ℕ) (x : Blocks m F) (q : ℕ),q≤3 →
      let ℓ := (D (j+d) []).ell
      let β := (D (j+d) []).width
      (‖iteratedFDeriv ℝ q (selectedFineFrontier m D d j I) x‖≤
        C^(d+1)*fineScale (ℓ*β^2) (ℓ*β) β q) ∧
      (∀ (c θ : ℝ),0<c → c≤1/128 → 1≤θ → ∀ p,p≤levels θ →
        ‖iteratedFDeriv ℝ q (selectedFinePiece m D d j I c θ p) x‖≤
          C^(d+1)*fineScale ((ℓ*β^2)*θ^(-amplitudeExponent p)) (ℓ*β)
            (pieceResolution c β θ p) q) := by
  obtain ⟨Cs,hCs,hselect⟩ := constructed_fine_selection_bound
  obtain ⟨Bp,hBp,hpieces⟩ := actual_joint_fine_piece_bounds
  obtain ⟨Bf,hBf,hfrontier⟩ := actual_joint_frontier_bounds
  have hCs0 : 0≤Cs := by linarith
  have hBp0 : 0≤Bp := by linarith
  have hBf0 : 0≤Bf := by linarith
  let C := Cs+Bp+Bf
  have hC : 1≤C := by unfold C;linarith
  have hC0 : 0≤C := by linarith
  have hCsC : Cs≤C := by unfold C;linarith
  have hBpC : Bp≤C := by unfold C;linarith
  have hBfC : Bf≤C := by unfold C;linarith
  refine ⟨C,hC,fun F _ _ _ initial hl hw r η b A K ζ cn CR hr hη hη1 hb hb1 hK hζ hζ1 hCR U => ?_⟩
  dsimp only
  let D := sourceGeometry initial r η b A K ζ cn CR U
  have hp := parentScale_positive initial r η hl hw hr hη
  have hadm (j : ℕ) (I : List ℕ) : NodeJetAdmissible (D j I) :=
    sourceNode_admissible A K ζ cn (η j) CR _ _ (r j) (b j) (U j I)
      hK hζ hζ1 (hη j) (hη1 j) hCR (hp j).1 (hp j).2 (hr j) (hb j) (hb1 j)
  have hmono := parentScale_width_antitone initial r η hl hw hr hη hη1
  intro d j I m x q hq
  let T := j+d
  let ℓ := (D T []).ell
  let β := (D T []).width
  have ht := hadm T []
  have hell : 0≤ℓ := ht.1
  have hβ : 0<β := ht.2.1
  have hβanc (k : ℕ) (P : List ℕ) (hk : k<T) : β≤(D k P).width :=
    hmono (by omega : k+1≤T+1)
  have transport (leaf : ℕ → List ℕ → Blocks m F → ℝ) (hleaf : ∀ k P,ContDiff ℝ 3 (leaf k P))
      (B a M δ : ℝ) (hB : 0≤B) (hBC : B≤C) (ha : 0≤a) (hM : 0≤M) (hδ : 0<δ)
      (hδβ : δ≤β) (haM : a≤M*β)
      (hbase : ∀ P y k,k≤3 → ‖iteratedFDeriv ℝ k (leaf T P) y‖≤B*fineScale a M δ k) :
      ‖iteratedFDeriv ℝ q (selectFamily m D leaf d j I) x‖≤C^(d+1)*fineScale a M δ q := by
    have hs := hselect F m D hadm leaf hleaf T B a M δ hB ha hM hδ
      (fun k P hk => ⟨hδβ.trans (hβanc k P hk),
        haM.trans (mul_le_mul_of_nonneg_left (hβanc k P hk) hM)⟩) hbase d j rfl I x q hq
    have hcoeff : Cs^d*B≤C^(d+1) := by
      calc
        _ ≤ C^d*C := mul_le_mul (pow_le_pow_left₀ hCs0 hCsC d) hBC hB (pow_nonneg hC0 d)
        _ = _ := (pow_succ C d).symm
    exact hs.trans (mul_le_mul_of_nonneg_right hcoeff (fineScale_nonneg ha hM hδ.le q))
  constructor
  · exact transport _ (fun k P => jointFineFrontier_contDiff m k (D k P))
      Bf (ℓ*β^2) (ℓ*β) β hBf0 hBfC (by positivity) (by positivity) hβ le_rfl (by nlinarith)
      (fun P y k hk => hfrontier F (D T P) (hadm T P).1 (hadm T P).2.1 (hadm T P).2.2.1 m T y k hk)
  · intro c θ hc hcs hθ p hpidx
    let δ := pieceResolution c β θ p
    have hδ : 0<δ := pieceResolution_pos c β θ hc hβ hθ p
    have hδβ : δ≤β := (pieceResolution_le c β θ hc.le hβ.le hθ p hpidx).trans
      (mul_le_of_le_one_left hβ.le (show c≤1 by linarith))
    have hexp : 0≤amplitudeExponent p := by
      unfold amplitudeExponent
      split_ifs
      · norm_num
      · exact aExponent_nonneg _
    have hθpow : θ^(-amplitudeExponent p)≤1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hθ (neg_nonpos.mpr hexp)
    have hamp : (ℓ*β^2)*θ^(-amplitudeExponent p)≤(ℓ*β)*β := by
      have hh := mul_le_mul_of_nonneg_left hθpow (show 0≤ℓ*β^2 by positivity)
      nlinarith only [hh]
    exact transport _ (fun k P => jointFinePiece_contDiff m k (D k P) c θ p)
      Bp ((ℓ*β^2)*θ^(-amplitudeExponent p)) (ℓ*β) δ hBp0 hBpC (by positivity) (by positivity)
      hδ hδβ hamp (fun P y k hk =>
        hpieces F (D T P) (hadm T P).1 (hadm T P).2.1 (hadm T P).2.2.1 c θ hc hcs hθ p hpidx m T y k hk)

end Bilevel.ChiCarrier
