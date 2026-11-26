import Bilevel.ChiSplitFineFlattening
import Bilevel.ChiFlattenComposition

/-! Sharp positive jets of the actual source-only flattened scalar profile.
The zero jet remains bounded while positive jets scale as delta^(1-k). -/
noncomputable section
namespace Bilevel.ChiSplitFine
open ChiBoundedChain ZeroChainPotential ZeroChainFlatteningCutoff

theorem flat_profile_jet_bounds : ∃ C : ℝ,1≤C ∧ ∀ (δ : ℝ),0<δ → δ≤1 →
    ∀ (j : Fin 4) (t : ℝ),|iteratedDeriv j.val (flatProfile δ) t|≤
      if j.val=0 then C else C/δ^(j.val-1) := by
  obtain ⟨P,hP,hprof⟩ := chain_profile_bound
  obtain ⟨K,hK,hcore⟩ := core_common_jet_bound
  let B := P*(K+1)^3
  have hP0 : 0≤P := by linarith only [hP]
  have hK0 : 0≤K := by linarith only [hK]
  have hpow : 1≤(K+1)^3 := by nlinarith only [hK0,sq_nonneg K,pow_nonneg hK0 3]
  have hPB : P≤B := by dsimp [B]; nlinarith only [mul_le_mul_of_nonneg_left hpow hP0]
  have hB : 1≤B := hP.trans hPB
  have hB0 : 0≤B := by linarith only [hB]
  let g : ℝ → ℝ := fun t => phi 0-phi t
  have hg : ContDiff ℝ 3 g := contDiff_const.sub (phi_contDiff 3)
  have houter (j : ℕ) (hj0 : 1≤j) (hj : j≤3) (t : ℝ) :
      ‖iteratedFDeriv ℝ j g t‖≤P := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs]
    change |iteratedDeriv j (fun u => phi 0-phi u) t|≤P
    rw [iteratedDeriv_const_sub (by omega)]
    change |iteratedDeriv j (fun u => -phi u) t|≤P
    rw [iteratedDeriv_neg,abs_neg]
    exact (hprof ⟨j,by omega⟩ t).2
  refine ⟨2*B,by linarith only [hB],fun δ hδ hδ1 j t => ?_⟩
  have hflat (k : ℕ) (hk0 : 1≤k) (hk : k≤3) :
      ‖iteratedFDeriv ℝ k (flatten δ) t‖≤K*δ/δ^k := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs]
    exact flatten_jet_bound hcore δ hδ k hk0 hk t
  have hf1 : ‖iteratedFDeriv ℝ 1 (flatten δ) t‖≤K := by
    convert hflat 1 (by norm_num) (by norm_num) using 1
    field_simp
  have hf2 : ‖iteratedFDeriv ℝ 2 (flatten δ) t‖≤K/δ := by
    convert hflat 2 (by norm_num) (by norm_num) using 1
    field_simp
    ring
  have hf3 : ‖iteratedFDeriv ℝ 3 (flatten δ) t‖≤K/δ^2 := by
    convert hflat 3 (by norm_num) (by norm_num) using 1
    field_simp
    ring
  have hb := ChiFlattenComposition.positive_jets (flatten δ) g (flatten_contDiff δ) hg P K δ
    hP0 hK0 hδ hδ1 t hf1 hf2 hf3
    (houter 1 (by norm_num) (by norm_num) _) (houter 2 (by norm_num) (by norm_num) _)
    (houter 3 (by norm_num) (by norm_num) _)
  have he : g ∘ flatten δ=flatProfile δ := by
    funext u
    dsimp [g,flatProfile,ChiFine.flatProfile]
    ring
  rw [he] at hb
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs] at hb
  fin_cases j
  · simp only [Fin.val_zero,iteratedDeriv_zero,if_pos rfl]
    change |-(phi (flatten δ t)-phi 0)|≤2*B
    rw [abs_neg]
    have h0 := (hprof 0 0).2
    have h1 := (hprof 0 (flatten δ t)).2
    simp only [Fin.val_zero,iteratedDeriv_zero] at h0 h1
    exact (abs_sub _ _).trans (by linarith only [h0,h1,hPB])
  · simp only [Fin.val_one,one_ne_zero,if_false,Nat.sub_self,pow_zero,div_one]
    exact hb.1.trans (by change B≤2*B; linarith only [hB0])
  · norm_num only [Fin.val_two,Nat.reduceSub,OfNat.ofNat_ne_zero,if_false,pow_one]
    exact hb.2.1.trans (div_le_div_of_nonneg_right (show B≤2*B by linarith only [hB0]) hδ.le)
  · norm_num only [Fin.val_mk,Nat.reduceSub,OfNat.ofNat_ne_zero,if_false]
    exact hb.2.2.trans (div_le_div_of_nonneg_right (show B≤2*B by linarith only [hB0]) (sq_nonneg δ))

end Bilevel.ChiSplitFine
