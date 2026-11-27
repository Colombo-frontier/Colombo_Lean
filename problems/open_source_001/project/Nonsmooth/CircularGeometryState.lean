import Nonsmooth.SubspaceCircularSection
import Nonsmooth.ShrinkingCircularRadii

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Histories are stored newest first; each entry determines one completed circular stage. -/
def circularGeometryState (R ε : ℝ) (N : ℕ) : List ℤ → E × Submodule ℝ E
  | [] => (0, ⊤)
  | j :: h =>
    let st := circularGeometryState R ε N h
    (subspaceCircularPoint st.2 st.1 (shrinkingCircularRadius R ε N h.length) N j,
      subspaceCircularSection st.2 N j)

def circularGeometryQuery (R ε : ℝ) (N : ℕ) (h : List ℤ) (j : ℤ) : E :=
  let st := circularGeometryState R ε N h
  subspaceCircularPoint st.2 st.1 (shrinkingCircularRadius R ε N h.length) N j

theorem circularGeometryQuery_anchor (R ε : ℝ) (N : ℕ) (h : List ℤ) :
    circularGeometryQuery (E := E) R ε N h 0 = (circularGeometryState R ε N h).1 :=
  subspaceCircularPoint_anchor _ _ _ N

theorem circularGeometryQuery_next (R ε : ℝ) (N : ℕ) (h : List ℤ) (j : ℤ) :
    (circularGeometryState (E := E) R ε N (j :: h)).1 = circularGeometryQuery R ε N h j := rfl

variable [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem circularGeometryQuery_periodic (R ε : ℝ) (N : ℕ) (h : List ℤ) :
    Function.Periodic (circularGeometryQuery (E := E) R ε N h) (4 * 2 ^ N) :=
  subspaceCircularPoint_periodic _ _ _ N

theorem circularGeometryState_norm_bound {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (N : ℕ) (h : List ℤ) :
    ‖(circularGeometryState (E := E) R ε N h).1‖ ≤
      (R / 2) * (1 - (circularRadiusRatio ε N) ^ h.length) := by
  induction h with
  | nil => simp [circularGeometryState]
  | cons j h ih =>
    let st := circularGeometryState (E := E) R ε N h
    let r := shrinkingCircularRadius R ε N h.length
    let β := circularRadiusRatio ε N
    have hβ0 : 0 ≤ β := (circularRadiusRatio_pos hε N).le
    have hβhalf : β ≤ 1 / 2 := circularRadiusRatio_le_half hε.le hε1 N
    have hr : 0 ≤ r := mul_nonneg (div_nonneg hR (by norm_num)) (pow_nonneg hβ0 _)
    have hmove := subspaceCircularPoint_displacement st.2 st.1 hr N j
    have hn : ‖subspaceCircularPoint st.2 st.1 r N j‖ ≤ ‖st.1‖ +
        ‖subspaceCircularPoint st.2 st.1 r N j - st.1‖ := by
      calc
        _ = ‖st.1 + (subspaceCircularPoint st.2 st.1 r N j - st.1)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hprod := mul_nonneg (mul_nonneg hR (pow_nonneg hβ0 h.length)) (sub_nonneg.mpr hβhalf)
    change ‖st.1‖ ≤ (R / 2) * (1 - β ^ h.length) at ih
    change ‖subspaceCircularPoint st.2 st.1 r N j‖ ≤ (R / 2) * (1 - β ^ (h.length + 1))
    rw [pow_succ]
    change ‖subspaceCircularPoint st.2 st.1 r N j - st.1‖ ≤ 2 * ((R / 8) * β ^ h.length) at hmove
    nlinarith only [ih, hn, hmove, hprod]

theorem circularGeometryState_norm_le_half {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (N : ℕ) (h : List ℤ) :
    ‖(circularGeometryState (E := E) R ε N h).1‖ ≤ R / 2 := by
  have hb := circularGeometryState_norm_bound (E := E) hR hε hε1 N h
  have hp := mul_nonneg (div_nonneg hR (by norm_num : (0 : ℝ) ≤ 2))
    (pow_nonneg (circularRadiusRatio_pos hε N).le h.length)
  nlinarith only [hb, hp]

theorem circularGeometryQuery_feasible {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (N : ℕ) (h : List ℤ) (j : ℤ) :
    ‖circularGeometryQuery (E := E) R ε N h j‖ ≤ R := by
  have heq := circularGeometryQuery_next (E := E) R ε N h j
  rw [← heq]
  exact (circularGeometryState_norm_le_half (E := E) hR hε hε1 N (j :: h)).trans (by linarith)

end
end Nonsmooth
