import Bilevel.CompensatedMeanCore

/-! Dimension-independent product-jet estimates for the actual clipped
coupling. Bounded overlap is used only after differentiating the displayed
finite sum, so no level-count factor appears. -/

noncomputable section
namespace Bilevel.CompensatedMean
open SmallGapProfiles SmallGapLiftSupport ZeroChainResidualBounds ZeroChainResidualJets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem linear_comp_jet_le {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (y : LowerSpace E) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (f ∘ uProj E) y‖ ≤ ‖iteratedFDeriv ℝ k f (uProj E y)‖ := by
  rw [(uProj E).iteratedFDeriv_comp_right hf y (by exact_mod_cast hk)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) uProj_opNorm_le)
    (norm_nonneg _)).trans_eq (mul_one _)

namespace Data
variable (P : Data (E := E))

def couplingTerm (j : ℕ) (y : LowerSpace E) : ℝ :=
  P.e j (uProj E y)*normal (P.w j) (sProj E y)

def coupling (y : LowerSpace E) : ℝ := ∑ j ∈ Finset.range (P.J+1),P.couplingTerm j y

theorem couplingTerm_contDiff (j : ℕ) (hj : j ≤ P.J) : ContDiff ℝ 3 (P.couplingTerm j) :=
  ((P.e_smooth j).comp (uProj E).contDiff).mul
    ((normal_contDiff (P.w j) (P.w_pos j hj)).comp (sProj E).contDiff)

theorem coupling_contDiff : ContDiff ℝ 3 P.coupling := by
  apply ContDiff.sum
  intro j hj
  exact P.couplingTerm_contDiff j (by have := Finset.mem_range.mp hj; omega)

def activePieces (u : E) : Finset ℕ := by
  classical
  exact (Finset.range (P.J+1)).filter (fun j => ∃ k : Fin 4,iteratedFDeriv ℝ k.val (P.e j) u ≠ 0)

theorem couplingTerm_flat (j : ℕ) (hj : j ≤ P.J) (y : LowerSpace E)
    (hn : j ∉ P.activePieces (uProj E y)) (k : ℕ) (hk : k ≤ 3) :
    iteratedFDeriv ℝ k (P.couplingTerm j) y = 0 := by
  classical
  have hflat (l : ℕ) (hl : l ≤ k) : iteratedFDeriv ℝ l (P.e j) (uProj E y) = 0 := by
    by_contra hh
    apply hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),⟨⟨l,by omega⟩,hh⟩⟩
  apply jet_mul_zero_left ((P.e_smooth j).comp (uProj E).contDiff)
    ((normal_contDiff (P.w j) (P.w_pos j hj)).comp (sProj E).contDiff) y k hk
  intro l hl
  apply flat_jet_comp (uProj E).contDiff (P.e_smooth j) y l (by omega)
  intro t ht
  rw [hflat t (by omega),norm_zero]

theorem couplingTerm_jet_bound (j : ℕ) (hj : j ≤ P.J) (y : LowerSpace E)
    (k : ℕ) (hk : k ≤ 3) (B : ℕ → ℝ) (hB : ∀ l,0 ≤ B l)
    (hb : ∀ l,l ≤ k → ‖iteratedFDeriv ℝ l (P.e j) (uProj E y)‖ ≤ B l) :
    ‖iteratedFDeriv ℝ k (P.couplingTerm j) y‖ ≤
      ∑ l ∈ Finset.range (k+1),(k.choose l:ℝ)*B l*(C*P.w j/P.w j^(k-l)) := by
  apply jet_mul_bound ((P.e_smooth j).comp (uProj E).contDiff)
    ((normal_contDiff (P.w j) (P.w_pos j hj)).comp (sProj E).contDiff) y k hk B
    (fun l => C*P.w j/P.w j^l) hB
  · intro l hl
    exact (linear_comp_jet_le (P.e_smooth j) y l (by omega)).trans (hb l hl)
  · intro l hl
    apply scalar_linear_jet_bound (normal_contDiff (P.w j) (P.w_pos j hj)) (sProj E)
      sProj_opNorm_le y l (by omega) (C*P.w j/P.w j^l)
    · have hw := P.w_pos j hj
      have hC := C_pos
      positivity
    · exact normal_C_bound (P.w j) (sProj E y) (P.w_pos j hj) ⟨l,by omega⟩

theorem couplingTerm_second_bound (j : ℕ) (hj : j ≤ P.J) (y : LowerSpace E)
    (A D₁ D₂ : ℝ) (hA : 0 ≤ A) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h0 : |P.e j (uProj E y)| ≤ A)
    (h1 : ‖iteratedFDeriv ℝ 1 (P.e j) (uProj E y)‖ ≤ D₁)
    (h2 : ‖iteratedFDeriv ℝ 2 (P.e j) (uProj E y)‖ ≤ D₂) :
    ‖iteratedFDeriv ℝ 2 (P.couplingTerm j) y‖ ≤ C*(A/P.w j+2*D₁+D₂*P.w j) := by
  let B : ℕ → ℝ := fun l => if l = 0 then A else if l = 1 then D₁ else D₂
  have hB (l : ℕ) : 0 ≤ B l := by dsimp [B]; split_ifs <;> assumption
  have hb (l : ℕ) (hl : l ≤ 2) : ‖iteratedFDeriv ℝ l (P.e j) (uProj E y)‖ ≤ B l := by
    interval_cases l
    · simpa [B,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h0
    · simpa [B] using h1
    · simpa [B] using h2
  have hh := P.couplingTerm_jet_bound j hj y 2 (by norm_num) B hB hb
  apply hh.trans_eq
  norm_num [Finset.sum_range_succ,B]
  field_simp [(P.w_pos j hj).ne']
  ring

theorem couplingTerm_third_bound (j : ℕ) (hj : j ≤ P.J) (y : LowerSpace E)
    (A D₁ D₂ D₃ : ℝ) (hA : 0 ≤ A) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hD₃ : 0 ≤ D₃)
    (h0 : |P.e j (uProj E y)| ≤ A)
    (h1 : ‖iteratedFDeriv ℝ 1 (P.e j) (uProj E y)‖ ≤ D₁)
    (h2 : ‖iteratedFDeriv ℝ 2 (P.e j) (uProj E y)‖ ≤ D₂)
    (h3 : ‖iteratedFDeriv ℝ 3 (P.e j) (uProj E y)‖ ≤ D₃) :
    ‖iteratedFDeriv ℝ 3 (P.couplingTerm j) y‖ ≤ C*(A/P.w j^2+3*D₁/P.w j+3*D₂+D₃*P.w j) := by
  let B : ℕ → ℝ := fun l => if l = 0 then A else if l = 1 then D₁ else if l = 2 then D₂ else D₃
  have hB (l : ℕ) : 0 ≤ B l := by dsimp [B]; split_ifs <;> assumption
  have hb (l : ℕ) (hl : l ≤ 3) : ‖iteratedFDeriv ℝ l (P.e j) (uProj E y)‖ ≤ B l := by
    interval_cases l
    · simpa [B,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h0
    · simpa [B] using h1
    · simpa [B] using h2
    · simpa [B] using h3
  have hh := P.couplingTerm_jet_bound j hj y 3 (by norm_num) B hB hb
  apply hh.trans_eq
  norm_num [Finset.sum_range_succ,B]
  field_simp [(P.w_pos j hj).ne']
  ring

/-- A uniform per-active-piece jet bound yields three times that bound for
the actual sum. The hypothesis is the explicitly proved overlap count. -/
theorem coupling_jet_bound (y : LowerSpace E) (k : ℕ) (hk : k ≤ 3) (D : ℝ) (hD : 0 ≤ D)
    (hoverlap : (P.activePieces (uProj E y)).card ≤ 3)
    (hterm : ∀ j,j ≤ P.J → ‖iteratedFDeriv ℝ k (P.couplingTerm j) y‖ ≤ D) :
    ‖iteratedFDeriv ℝ k P.coupling y‖ ≤ 3*D := by
  classical
  let S := P.activePieces (uProj E y)
  have hsub : S ⊆ Finset.range (P.J+1) := Finset.filter_subset _ _
  have he : (∑ j ∈ S,iteratedFDeriv ℝ k (P.couplingTerm j) y) =
      ∑ j ∈ Finset.range (P.J+1),iteratedFDeriv ℝ k (P.couplingTerm j) y := by
    apply Finset.sum_subset hsub
    intro j hj hn
    exact P.couplingTerm_flat j (by have := Finset.mem_range.mp hj; omega) y hn k hk
  change ‖iteratedFDeriv ℝ k (fun v => ∑ j ∈ Finset.range (P.J+1),P.couplingTerm j v) y‖ ≤ _
  rw [iteratedFDeriv_sum (fun j hj => (P.couplingTerm_contDiff j
    (by have := Finset.mem_range.mp hj; omega)).of_le (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  rw [← he]
  calc
    _ ≤ ∑ j ∈ S,‖iteratedFDeriv ℝ k (P.couplingTerm j) y‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ S,D := Finset.sum_le_sum (fun j hj => hterm j
      (by have := Finset.mem_range.mp (hsub hj); omega))
    _ = (S.card:ℝ)*D := by simp
    _ ≤ 3*D := mul_le_mul_of_nonneg_right (by exact_mod_cast hoverlap) hD

end Data
end Bilevel.CompensatedMean
