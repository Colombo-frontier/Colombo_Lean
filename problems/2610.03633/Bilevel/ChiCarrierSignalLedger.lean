import Bilevel.ChiCarrierFineLedger
import Bilevel.ChiFineSignalBounds

/-! The actual globally fixed residual difference, after radial/frame
composition and every inner ancestor selector. Its small value scale is
retained separately from its positive derivative scales. -/
noncomputable section
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def jointFineSignal (m j : ℕ) (D : Node E) (τ : ℝ) : Blocks m E → ℝ :=
  (ChiFine.signalResidual D.n D.ell D.width τ ∘ D.coordinates) ∘ block m j

theorem jointFineSignal_contDiff (m j : ℕ) (D : Node E) (τ : ℝ) :
    ContDiff ℝ 3 (jointFineSignal m j D τ) :=
  ((ChiFine.signalResidual_contDiff D.n D.ell D.width τ).comp (D.coordinates_contDiff 3)).comp
    (block (E:=E) m j).contDiff

def selectedFineFlatFrontier (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (τ : ℝ) : Blocks m E → ℝ :=
  selectFamily m D (fun j I => jointFineFlatFrontier m j (D j I) τ) d j I

def selectedFineSignal (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (τ : ℝ) : Blocks m E → ℝ :=
  selectFamily m D (fun j I => jointFineSignal m j (D j I) τ) d j I

theorem selectedFineSignal_contDiff (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (τ : ℝ) :
    ContDiff ℝ 3 (selectedFineSignal m D d j I τ) :=
  selectFamily_contDiff m D _ (fun j I => jointFineSignal_contDiff m j (D j I) τ) d j I

theorem selectedFineSignal_eq_sub (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) (τ : ℝ)
    (x : Blocks m E) :
    selectedFineSignal m D d j I τ x=selectedFineFrontier m D d j I x-selectedFineFlatFrontier m D d j I τ x :=
  selectFamily_sub m D (fun j I => jointFineFrontier m j (D j I))
    (fun j I => jointFineFlatFrontier m j (D j I) τ) d j I x

theorem actual_joint_signal_bounds : ∃ B : ℝ,1≤B ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (D : Node F),0≤D.ell → 0<D.width → D.width≤D.radius →
      ∀ τ,0<τ → τ≤D.width/16 → ∀ (m j : ℕ) (x : Blocks m F) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (jointFineSignal m j D τ) x‖≤
        B*fineScale ((D.ell*D.width)*τ) (D.ell*D.width) τ q := by
  obtain ⟨B,hB,hraw⟩ := ChiFine.signal_residual_bounds
  have hB0 : 0≤B := by linarith
  refine ⟨100000*(2*B),by linarith,fun F _ _ _ D hell hh hhR τ hτ hτh m j x q hq => ?_⟩
  have hτR : τ≤D.radius := (show τ≤D.width by linarith).trans hhR
  have hb : ∀ k,k≤3 → ∀ z,‖iteratedFDeriv ℝ k (ChiFine.signalResidual D.n D.ell D.width τ) z‖≤
      (2*B)*fineScale ((D.ell*D.width)*τ) (D.ell*D.width) τ k := by
    intro k hk z
    have ht := hraw D.n D.ell D.width τ hell hh hτ hτh z
    cases k with
    | zero =>
      rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
      apply ht.1.trans
      dsimp [fineScale]
      nlinarith only [show 0≤B*D.ell*D.width*τ by positivity]
    | succ k =>
      exact (ht.2 ⟨k,by omega⟩).trans_eq (by dsimp [fineScale];ring)
  exact radial_fine_leaf_bound (ChiFine.signalResidual_contDiff D.n D.ell D.width τ)
    (2*B) _ _ τ D.radius (by positivity) (by positivity) (by positivity) hτ hτR hb D.frame m j x q hq

theorem source_selected_signal_ledger : ∃ C : ℝ,1≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (A K ζ cn CR : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,0<b j) → (∀ j,b j≤1) → 1≤K → 0<ζ → ζ≤1 → 1≤CR →
      ∀ (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let D := sourceGeometry initial r η b A K ζ cn CR U
      ∀ (d j : ℕ) (I : List ℕ) (m : ℕ) (τ : ℝ),0<τ → τ≤(D (j+d) []).width/16 →
      ∀ (x : Blocks m F) (q : ℕ),q≤3 →
      let ℓ := (D (j+d) []).ell
      let β := (D (j+d) []).width
      ‖iteratedFDeriv ℝ q (selectedFineSignal m D d j I τ) x‖≤
        C^(d+1)*fineScale ((ℓ*β)*τ) (ℓ*β) τ q := by
  obtain ⟨Cs,hCs,hselect⟩ := constructed_fine_selection_bound
  obtain ⟨B,hB,hbase⟩ := actual_joint_signal_bounds
  have hCs0 : 0≤Cs := by linarith
  have hB0 : 0≤B := by linarith
  let C := Cs+B
  have hC : 1≤C := by unfold C;linarith
  have hC0 : 0≤C := by linarith
  have hCsC : Cs≤C := by unfold C;linarith
  have hBC : B≤C := by unfold C;linarith
  refine ⟨C,hC,fun F _ _ _ initial hl hw r η b A K ζ cn CR hr hη hη1 hb hb1 hK hζ hζ1 hCR U => ?_⟩
  dsimp only
  let D := sourceGeometry initial r η b A K ζ cn CR U
  have hp := parentScale_positive initial r η hl hw hr hη
  have hadm (j : ℕ) (I : List ℕ) : NodeJetAdmissible (D j I) :=
    sourceNode_admissible A K ζ cn (η j) CR _ _ (r j) (b j) (U j I)
      hK hζ hζ1 (hη j) (hη1 j) hCR (hp j).1 (hp j).2 (hr j) (hb j) (hb1 j)
  have hmono := parentScale_width_antitone initial r η hl hw hr hη hη1
  intro d j I m τ hτ hτβ x q hq
  let T := j+d
  let ℓ := (D T []).ell
  let β := (D T []).width
  have ht := hadm T []
  have hell : 0≤ℓ := ht.1
  have hβ : 0<β := ht.2.1
  have hτβ' : τ≤β := by change τ≤β/16 at hτβ;linarith
  have hanc (k : ℕ) (P : List ℕ) (hk : k<T) : τ≤(D k P).width :=
    hτβ'.trans (hmono (by omega : k+1≤T+1))
  have hs := hselect F m D hadm (fun j I => jointFineSignal m j (D j I) τ)
    (fun j I => jointFineSignal_contDiff m j (D j I) τ) T B ((ℓ*β)*τ) (ℓ*β) τ
    hB0 (by positivity) (by positivity) hτ
    (fun k P hk => ⟨hanc k P hk,mul_le_mul_of_nonneg_left (hanc k P hk) (by positivity)⟩)
    (fun P y k hk => hbase F (D T P) (hadm T P).1 (hadm T P).2.1 (hadm T P).2.2.1
      τ hτ hτβ m T y k hk) d j rfl I x q hq
  have hcoeff : Cs^d*B≤C^(d+1) := by
    calc
      _ ≤ C^d*C := mul_le_mul (pow_le_pow_left₀ hCs0 hCsC d) hBC hB0 (pow_nonneg hC0 d)
      _ = _ := (pow_succ C d).symm
  exact hs.trans (mul_le_mul_of_nonneg_right hcoeff (fineScale_nonneg (by positivity) (by positivity) hτ.le q))

end Bilevel.ChiCarrier
