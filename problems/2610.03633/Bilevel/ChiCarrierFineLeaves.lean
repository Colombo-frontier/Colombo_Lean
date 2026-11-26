import Bilevel.ChiCarrierFineSelection
import Bilevel.ChiFineCouplingCore

/-! Actual scheduled fine pieces after radial compression, frame mapping,
and embedding into the joint finite Hilbert product. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive ZeroChainSchedule

theorem radial_fine_leaf_bound
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 3 f)
    (B a M δ R : ℝ) (hB : 0≤B) (ha : 0≤a) (hM : 0≤M) (hδ : 0<δ) (hδR : δ≤R)
    (hb : ∀ k,k≤3 → ∀ z,‖iteratedFDeriv ℝ k f z‖≤B*fineScale a M δ k)
    (U : Space n →ₗᵢ[ℝ] F) (m j : ℕ) (x : Blocks m F) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k ((f ∘ WrappedChain.coordinates n R U) ∘ block m j) x‖≤
      (100000*B)*fineScale a M δ k := by
  have hc := hf.comp (ZeroChainWrappedResidual.coordinates_contDiff n R U)
  apply (block_jet_contraction m j hc x k hk).trans
  by_cases hk0 : k=0
  · subst k
    rw [norm_iteratedFDeriv_zero]
    have hz := hb 0 (by norm_num) (WrappedChain.coordinates n R U (block m j x))
    rw [norm_iteratedFDeriv_zero] at hz
    exact hz.trans (by dsimp [fineScale];nlinarith only [mul_nonneg hB ha])
  · obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hs : s≤2 := by omega
    have hout : ∀ q,1≤q → q≤3 → ∀ z,‖iteratedFDeriv ℝ q f z‖≤(B*M)*δ/δ^q := by
      intro q hq0 hq z
      obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
      have ht := hb (t+1) hq z
      apply ht.trans_eq
      simp only [fineScale,pow_succ]
      field_simp
      ring
    have hin : ∀ q,1≤q → q≤3 → ∀ u : F,
        ‖iteratedFDeriv ℝ q (WrappedChain.coordinates n R U) u‖≤24*δ/δ^q := by
      intro q hq0 hq u
      exact ZeroChainWrappedResidual.coordinates_positive_jet_bound n R δ hδ hδR U u q hq0 hq
    have hcomp := ZeroChainCarry.positive_composition_jet_bound hf
      (ZeroChainWrappedResidual.coordinates_contDiff n R U) 24 (B*M) δ
      (by norm_num) (by positivity) hδ hout hin (block m j x) (s+1) (by omega) hk
    have hfct : ((s+1).factorial:ℝ)*24^(s+1)≤100000 := by interval_cases s <;> norm_num
    have hbound := mul_le_mul_of_nonneg_right hfct (show 0≤B*M/δ^s by positivity)
    apply hcomp.trans
    convert hbound using 1 <;> simp only [fineScale,pow_succ] <;> field_simp <;> ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def jointFineFrontier (m j : ℕ) (D : Node E) : Blocks m E → ℝ :=
  (ChiFine.frontier D.n D.ell D.width ∘ D.coordinates) ∘ block m j

def jointFineFlatFrontier (m j : ℕ) (D : Node E) (τ : ℝ) : Blocks m E → ℝ :=
  (ChiFine.flatFrontier D.n D.ell D.width τ ∘ D.coordinates) ∘ block m j

def jointFinePiece (m j : ℕ) (D : Node E) (c θ : ℝ) (i : ℕ) : Blocks m E → ℝ :=
  ((ZeroChainResidualScaled.scaled (ChiFine.piece D.n (levels θ) (resolution c 1 θ) i)
    (D.ell*D.width^2) D.width) ∘ D.coordinates) ∘ block m j

theorem jointFineFrontier_contDiff (m j : ℕ) (D : Node E) : ContDiff ℝ 3 (jointFineFrontier m j D) :=
  ((ChiFine.frontier_contDiff D.n D.ell D.width).comp (D.coordinates_contDiff 3)).comp
    (block (E:=E) m j).contDiff

theorem jointFineFlatFrontier_contDiff (m j : ℕ) (D : Node E) (τ : ℝ) :
    ContDiff ℝ 3 (jointFineFlatFrontier m j D τ) :=
  ((ChiFine.flatFrontier_contDiff D.n D.ell D.width τ).comp (D.coordinates_contDiff 3)).comp
    (block (E:=E) m j).contDiff

theorem jointFinePiece_contDiff (m j : ℕ) (D : Node E) (c θ : ℝ) (i : ℕ) :
    ContDiff ℝ 3 (jointFinePiece m j D c θ i) :=
  ((ZeroChainResidualScaled.scaled_contDiff (ChiFine.piece_contDiff D.n (levels θ) (resolution c 1 θ) i)
    (D.ell*D.width^2) D.width).comp (D.coordinates_contDiff 3)).comp (block (E:=E) m j).contDiff

theorem jointFinePiece_sum (m j : ℕ) (D : Node E) (c θ : ℝ) (x : Blocks m E) :
    (∑ i : Fin (levels θ+1),jointFinePiece m j D c θ i.val x)=jointFineFrontier m j D x := by
  rw [Fin.sum_univ_eq_sum_range (fun i => jointFinePiece m j D c θ i x) (levels θ+1)]
  simp only [jointFinePiece,jointFineFrontier,Function.comp_apply,ZeroChainResidualScaled.scaled]
  rw [← Finset.mul_sum,ChiFine.sum_piece]
  rfl

theorem actual_joint_fine_piece_bounds : ∃ B : ℝ,1≤B ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (D : Node F),0≤D.ell → 0<D.width → D.width≤D.radius →
      ∀ (c θ : ℝ),0<c → c≤1/128 → 1≤θ → ∀ (i : ℕ),i≤levels θ →
      ∀ (m j : ℕ) (x : Blocks m F) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (jointFinePiece m j D c θ i) x‖≤
        B*fineScale ((D.ell*D.width^2)*θ^(-amplitudeExponent i)) (D.ell*D.width)
          (pieceResolution c D.width θ i) q := by
  obtain ⟨B,hB,hpiece⟩ := ChiFine.actual_piece_budgets
  have hB0 : 0≤B := by linarith
  refine ⟨100000*B,by linarith,fun F _ _ _ D hell hh hhR c θ hc hcs hθ i hi m j x q hq => ?_⟩
  let P : ChiFine.Parameters := ⟨D.ell,D.width,θ,c,hell,hh,hθ,hc,hcs⟩
  let δ := pieceResolution c D.width θ i
  have hδ : 0<δ := pieceResolution_pos c D.width θ hc hh hθ i
  have hδR : δ≤D.radius := (pieceResolution_le c D.width θ hc.le hh.le hθ i hi).trans
    ((mul_le_of_le_one_left hh.le (show c≤1 by linarith)).trans hhR)
  have hraw : ∀ k,k≤3 → ∀ z,‖iteratedFDeriv ℝ k (P.pieces D.n i) z‖≤
      B*fineScale ((D.ell*D.width^2)*θ^(-amplitudeExponent i)) (D.ell*D.width) δ k := by
    intro k hk z
    have hb := hpiece P D.n i hi z
    cases k with
    | zero =>
      rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
      exact hb.1.trans_eq (by dsimp [fineScale,P,ChiFine.Parameters.amplitude];ring)
    | succ k =>
      have ht := hb.2 ⟨k,by omega⟩
      apply ht.trans_eq
      dsimp only [fineScale,P,ChiFine.Parameters.amplitude,δ]
      field_simp
      ring
  exact radial_fine_leaf_bound (P.pieces_contDiff D.n i) B _ _ δ D.radius hB0
    (by positivity) (by positivity) hδ hδR hraw D.frame m j x q hq

theorem actual_joint_frontier_bounds : ∃ B : ℝ,1≤B ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (D : Node F),0≤D.ell → 0<D.width → D.width≤D.radius →
      ∀ (m j : ℕ) (x : Blocks m F) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (jointFineFrontier m j D) x‖≤
        B*fineScale (D.ell*D.width^2) (D.ell*D.width) D.width q := by
  obtain ⟨B,hB,hfrontier⟩ := ChiFine.source_frontier_jet_bounds
  have hB0 : 0≤B := by linarith
  refine ⟨100000*B,by linarith,fun F _ _ _ D hell hh hhR m j x q hq => ?_⟩
  have hraw : ∀ k,k≤3 → ∀ z,‖iteratedFDeriv ℝ k (ChiFine.frontier D.n D.ell D.width) z‖≤
      B*fineScale (D.ell*D.width^2) (D.ell*D.width) D.width k := by
    intro k hk z
    apply (hfrontier D.n k D.ell D.width hk hell hh z).trans_eq
    cases k with
    | zero => simp only [fineScale,pow_zero,div_one];ring
    | succ k => simp only [fineScale,pow_succ];field_simp;ring
  exact radial_fine_leaf_bound (ChiFine.frontier_contDiff D.n D.ell D.width) B _ _ D.width D.radius hB0
    (by positivity) (by positivity) hh hhR hraw D.frame m j x q hq

end Bilevel.ChiCarrier
