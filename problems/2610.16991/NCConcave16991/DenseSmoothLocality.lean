import NCConcave16991.DenseSmoothConstruction
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Exact first-jet locality of the actual dense radial components -/

noncomputable section

namespace NCConcave16991.DenseSmooth

open scoped BigOperators InnerProductSpace ContDiff

set_option maxHeartbeats 700000
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n T : ℕ}

def link (ρ : ℝ) (u : Fin (T + 1) → E) (rows : Fin n → Fin (T + 1) → E)
    (i : Fin n) (j : Fin T) (x : Blocks E T) : ℝ :=
  gate (coordinate u x j.castSucc) * (scaledRadialCoordinate ρ (rows i j.succ) (x j.succ) + 1)

def truncatedChain (h : ℕ) (ρ : ℝ) (u : Fin (T + 1) → E)
    (rows : Fin n → Fin (T + 1) → E) (i : Fin n) (x : Blocks E T) : ℝ :=
  -scaledRadialCoordinate ρ (rows i 0) (x 0) -
    ∑ j : Fin T, (if j.val < h then link ρ u rows i j x else 0) + (33 / 32 : ℝ) * ‖x‖ ^ 2

theorem link_contDiff (ρ : ℝ) (u : Fin (T + 1) → E)
    (rows : Fin n → Fin (T + 1) → E) (i : Fin n) (j : Fin T) :
    ContDiff ℝ ∞ (link ρ u rows i j) :=
  (gate_contDiff.comp (coordinate_contDiff u j.castSucc)).mul
    ((contDiff_const.mul (coordinate_contDiff (rows i) j.succ)).add contDiff_const)

theorem link_firstJet_zero (ρ : ℝ) (u : Fin (T + 1) → E)
    (rows : Fin n → Fin (T + 1) → E) (i : Fin n) (j : Fin T) (x : Blocks E T)
    (hflat : coordinate u x j.castSucc ≤ 5 / 32) :
    link ρ u rows i j x = 0 ∧ fderiv ℝ (link ρ u rows i j) x = 0 := by
  have hg := (gate_hasDerivAt (coordinate u x j.castSucc)).comp_hasFDerivAt x
    ((coordinate_contDiff u j.castSucc).differentiable (by simp) x).hasFDerivAt
  have hr := (((coordinate_contDiff (rows i) j.succ).differentiable (by simp) x).hasFDerivAt.const_mul ρ⁻¹).add_const 1
  have hh := hg.mul hr
  constructor
  · simp only [link, gate_zero hflat, zero_mul]
  · change HasFDerivAt (link ρ u rows i j) _ x at hh
    rw [hh.fderiv]
    simp only [Function.comp_apply, gate_zero hflat, gateD_zero_left hflat, zero_smul,
      smul_zero, add_zero]

theorem component_firstJet_eq_truncated (h : ℕ) (ρ : ℝ) (u : Fin (T + 1) → E)
    (rows : Fin n → Fin (T + 1) → E) (i : Fin n) (x : Blocks E T)
    (hflat : ∀ j : Fin T, h ≤ j.val → coordinate u x j.castSucc ≤ 5 / 32) :
    componentChain ρ u rows i x = truncatedChain h ρ u rows i x ∧
      gradient (componentChain ρ u rows i) x = gradient (truncatedChain h ρ u rows i) x := by
  have hv (j : Fin T) : link ρ u rows i j x = (if j.val < h then link ρ u rows i j x else 0) := by
    split_ifs with hj
    · rfl
    · exact (link_firstJet_zero ρ u rows i j x (hflat j (by omega))).1
  have hd (j : Fin T) : HasFDerivAt
      (fun z : Blocks E T ↦ if j.val < h then link ρ u rows i j z else 0)
      (fderiv ℝ (link ρ u rows i j) x) x := by
    by_cases hj : j.val < h
    · simpa only [hj, ite_true] using ((link_contDiff ρ u rows i j).differentiable (by simp) x).hasFDerivAt
    · rw [(link_firstJet_zero ρ u rows i j x (hflat j (by omega))).2]
      simpa only [hj, ite_false] using hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x
  have hr := ((coordinate_contDiff (rows i) 0).differentiable (by simp) x).hasFDerivAt.const_mul ρ⁻¹
  have hq := ((hasFDerivAt_id x).norm_sq).const_mul (33 / 32 : ℝ)
  have hfull := (hr.neg.sub (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ ↦ ((link_contDiff ρ u rows i j).differentiable (by simp) x).hasFDerivAt))).add hq
  have htrunc := (hr.neg.sub (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hd j))).add hq
  change HasFDerivAt (componentChain ρ u rows i) _ x at hfull
  change HasFDerivAt (truncatedChain h ρ u rows i) _ x at htrunc
  constructor
  · unfold componentChain truncatedChain
    congr 2
    exact Finset.sum_congr rfl (fun j _ ↦ hv j)
  · apply (InnerProductSpace.toDual ℝ (Blocks E T)).injective
    rw [toDual_gradient, toDual_gradient, hfull.fderiv, htrunc.fderiv]

theorem truncatedChain_eq_of_known_data (h : ℕ) (ρ : ℝ)
    (u v : Fin (T + 1) → E) (rows rows' : Fin n → Fin (T + 1) → E) (i : Fin n)
    (hu : ∀ j, j.val < h → u j = v j)
    (hr : ∀ j, j.val ≤ h → rows i j = rows' i j) :
    truncatedChain h ρ u rows i = truncatedChain h ρ v rows' i := by
  funext x
  unfold truncatedChain
  rw [hr 0 (by simp)]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · unfold link coordinate
    rw [hu j.castSucc hj, hr j.succ (by simp only [Fin.val_succ]; omega)]
  · rfl

end NCConcave16991.DenseSmooth
