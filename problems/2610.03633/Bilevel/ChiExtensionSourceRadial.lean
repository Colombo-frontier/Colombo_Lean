import Bilevel.ChiExtensionRadialSum
import Bilevel.ChiRecursiveSourceGeometry
import Bilevel.ChiExtensionCalibration

/-! Actual public radial extension instantiated with the recursive source
coefficient and radius. The inverse lower-weight in the radius cancels
exactly from every Hessian budget. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiExtension PrimitiveGeometry

theorem source_radial_coefficient_radius {CR lp hp r b ζ : ℝ}
    (hlp : 0 < lp) (hb : 0 < b) (hζ : 0 < ζ) :
    (b*(ζ*lp))*sourceLocalRadius CR lp hp r b ζ = CR*(lp*hp)*Real.sqrt r := by
  unfold sourceLocalRadius
  field_simp

theorem source_radial_radius_pos {CR lp hp r b ζ : ℝ}
    (hCR : 0 < CR) (hlp : 0 < lp) (hhp : 0 < hp) (hr : 0 < r)
    (hb : 0 < b) (hζ : 0 < ζ) : 0 < sourceLocalRadius CR lp hp r b ζ := by
  unfold sourceLocalRadius
  positivity

theorem source_radialSum_jets
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {n m : ℕ} (index : Fin n → Fin m) (L : Fin n → E →L[ℝ] F) (hL : ∀ j,‖L j‖ ≤ 1)
    (lp hp r b : Fin n → ℝ) (CR ζ d : ℝ)
    (hlp : ∀ j,0 < lp j) (hhp : ∀ j,0 < hp j) (hr : ∀ j,0 < r j)
    (hb : ∀ j,0 < b j) (hCR : 0 < CR) (hζ : 0 < ζ) (hd : 0 < d) (z : Full E m) :
    let ν := fun j => b j*(ζ*lp j)
    let R := fun j => sourceLocalRadius CR (lp j) (hp j) (r j) (b j) ζ
    ‖iteratedFDeriv ℝ 2 (radialSum index L hL ν R d) z‖ ≤
      ∑ j : Fin n,3*CR*(lp j*hp j)*Real.sqrt (r j)/d ∧
    ‖iteratedFDeriv ℝ 3 (radialSum index L hL ν R d) z‖ ≤
      ∑ j : Fin n,9*b j*ζ*lp j/d := by
  dsimp only
  have hh := radialSum_jets index L hL (fun j => b j*(ζ*lp j))
    (fun j => sourceLocalRadius CR (lp j) (hp j) (r j) (b j) ζ) d
    (fun j => mul_nonneg (hb j).le (mul_nonneg hζ.le (hlp j).le))
    (fun j => source_radial_radius_pos hCR (hlp j) (hhp j) (hr j) (hb j) hζ) hd z
  constructor
  · apply hh.1.trans_eq
    apply Finset.sum_congr rfl
    intro j _
    rw [source_radial_coefficient_radius (hlp j) (hb j) hζ]
    ring
  · apply hh.2.trans_eq
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem source_radialSum_uniform_budgets
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {n m : ℕ} (index : Fin n → Fin m) (L : Fin n → E →L[ℝ] F) (hL : ∀ j,‖L j‖ ≤ 1)
    (lp hp r b : Fin n → ℝ) (CR ζ d forceBudget curvatureBudget : ℝ)
    (hlp : ∀ j,0 < lp j) (hhp : ∀ j,0 < hp j) (hr : ∀ j,0 < r j)
    (hb : ∀ j,0 < b j) (hb1 : ∀ j,b j ≤ 1) (hCR : 0 < CR) (hζ : 0 < ζ) (hd : 0 < d)
    (hforce : ∀ j,lp j*hp j*Real.sqrt (r j) ≤ forceBudget)
    (hcurv : ∀ j,lp j ≤ curvatureBudget) (z : Full E m) :
    let ν := fun j => b j*(ζ*lp j)
    let R := fun j => sourceLocalRadius CR (lp j) (hp j) (r j) (b j) ζ
    ‖iteratedFDeriv ℝ 2 (radialSum index L hL ν R d) z‖ ≤ (n:ℝ)*(3*CR*forceBudget/d) ∧
    ‖iteratedFDeriv ℝ 3 (radialSum index L hL ν R d) z‖ ≤ (n:ℝ)*(9*ζ*curvatureBudget/d) := by
  dsimp only
  have hj := source_radialSum_jets index L hL lp hp r b CR ζ d hlp hhp hr hb hCR hζ hd z
  constructor
  · apply hj.1.trans
    calc
      _ ≤ ∑ _ : Fin n,3*CR*forceBudget/d := by
        apply Finset.sum_le_sum
        intro j _
        have hh := mul_le_mul_of_nonneg_left (hforce j) (show 0 ≤ 3*CR/d by positivity)
        convert hh using 1 <;> ring
      _ = _ := by simp
  · apply hj.2.trans
    calc
      _ ≤ ∑ _ : Fin n,9*ζ*curvatureBudget/d := by
        apply Finset.sum_le_sum
        intro j _
        have hc : b j*lp j ≤ curvatureBudget :=
          (mul_le_mul_of_nonneg_right (hb1 j) (hlp j).le).trans (by simpa using hcurv j)
        have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 9*ζ/d by positivity)
        convert hh using 1 <;> ring
      _ = _ := by simp

end Bilevel.ChiExtensionCalibration
