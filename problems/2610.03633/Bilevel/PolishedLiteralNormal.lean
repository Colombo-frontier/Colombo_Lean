import Bilevel.ChiBoundedChainMasks
import Bilevel.ZeroChainResidualCutoffs

/-! A genuine C-infinity odd compact normal profile permitted by the literal
manuscript. It is not the finite-order septic normal used by the older
CompensatedMean implementation. -/
noncomputable section
namespace Bilevel.PolishedLiteral

def normalCutoff (t : ℝ) : ℝ :=
  1-Real.smoothTransition ((16*t^2-1)/3)

def normal (t : ℝ) : ℝ := t*normalCutoff t

def normalAtWidth (w s : ℝ) : ℝ := w*normal (s/w)

theorem normalCutoff_contDiff {k : ℕ∞} : ContDiff ℝ k normalCutoff :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul (contDiff_id.pow 2)).sub contDiff_const).div_const 3))

theorem normal_contDiff {k : ℕ∞} : ContDiff ℝ k normal :=
  contDiff_id.mul normalCutoff_contDiff

theorem normalAtWidth_contDiff (w : ℝ) {k : ℕ∞} : ContDiff ℝ k (normalAtWidth w) :=
  contDiff_const.mul (normal_contDiff.comp (contDiff_id.div_const w))

theorem normalCutoff_one {t : ℝ} (ht : |t|≤1/4) : normalCutoff t=1 := by
  have hh := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at hh
  simp only [normalCutoff,Real.smoothTransition.zero_of_nonpos (by nlinarith : (16*t^2-1)/3≤0),sub_zero]

theorem normalCutoff_zero {t : ℝ} (ht : 1/2≤|t|) : normalCutoff t=0 := by
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) ht 2
  rw [sq_abs] at hh
  simp only [normalCutoff,Real.smoothTransition.one_of_one_le (by nlinarith : 1≤(16*t^2-1)/3),sub_self]

theorem normal_eq_self {t : ℝ} (ht : |t|≤1/4) : normal t=t := by
  rw [normal,normalCutoff_one ht,mul_one]

theorem normal_zero {t : ℝ} (ht : 1/2≤|t|) : normal t=0 := by
  rw [normal,normalCutoff_zero ht,mul_zero]

theorem normal_odd : ∀ t : ℝ,normal (-t) = -normal t := by
  intro t
  simp only [normal,normalCutoff,neg_sq,neg_mul]

theorem normal_compactSupport : HasCompactSupport normal := by
  apply SmallGapProfileBounds.compactSupport_of_tail (1/2)
  intro t ht
  exact normal_zero ht

theorem normalAtWidth_eq_self {w s : ℝ} (hw : 0<w) (hs : |s|≤w/4) :
    normalAtWidth w s=s := by
  have hh : |s/w|≤1/4 := by
    rw [abs_div,abs_of_pos hw]
    exact (div_le_iff₀ hw).mpr (by linarith)
  rw [normalAtWidth,normal_eq_self hh]
  field_simp

theorem normalAtWidth_deriv_core {w s : ℝ} (hw : 0<w) (hs : |s|≤w/4) :
    deriv (normalAtWidth w) s=1 := by
  let f : ℝ → ℝ := fun t => normalAtWidth w t-t
  have hd : DifferentiableAt ℝ f s :=
    ((normalAtWidth_contDiff w (k:=1)).differentiable (by norm_num) s).sub differentiableAt_id
  have hz : deriv f s=0 := ZeroChainResidualCutoffs.deriv_zero_of_constant_on hd
    (uniqueDiffOn_Icc (by linarith : -(w/4)<w/4))
    (fun t ht => sub_eq_zero.mpr (normalAtWidth_eq_self hw (abs_le.mpr ht))) (abs_le.mp hs)
  have he : deriv f s=deriv (normalAtWidth w) s-1 := by
    exact ((normalAtWidth_contDiff w (k:=1)).differentiable (by norm_num) s).hasDerivAt.sub
      (hasDerivAt_id s) |>.deriv
  linarith

end Bilevel.PolishedLiteral

namespace Bilevel.PolishedLiteral

theorem normal_common_bound : ∃ C : ℝ,1≤C ∧
    ∀ (j : Fin 4) (s : ℝ),|iteratedDeriv j.val normal s|≤C := by
  classical
  choose A hA hbound using (fun j : Fin 4 =>
    SmallGapProfileBounds.compact_c3_bound normal_compactSupport (normal_contDiff (k:=3)) j.val (by omega))
  refine ⟨1+∑ j,A j,le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hA j)),?_⟩
  intro j s
  have hj := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hA j) (Finset.mem_univ j)
  exact (hbound j s).trans (by linarith)

noncomputable def normalJetConstant : ℝ := Classical.choose normal_common_bound

theorem normalJetConstant_one_le : 1≤normalJetConstant :=
  (Classical.choose_spec normal_common_bound).1

theorem normalAtWidth_C_bound (w s : ℝ) (hw : 0<w) (j : Fin 4) :
    |iteratedDeriv j.val (normalAtWidth w) s|≤normalJetConstant*w/w^j.val := by
  have he : normalAtWidth w=fun t => w*normal (t/w) := rfl
  rw [he,SmallGapProfileBounds.iteratedDeriv_scaled
    ((normal_contDiff (k:=3)).of_le (by exact_mod_cast (show j.val≤3 by omega))) w w s,
    abs_mul,abs_of_pos (div_pos hw (pow_pos hw _))]
  have hb := (Classical.choose_spec normal_common_bound).2 j (s/w)
  exact (mul_le_mul_of_nonneg_left hb (by positivity : 0≤w/w^j.val)).trans_eq (by unfold normalJetConstant;ring)

end Bilevel.PolishedLiteral
