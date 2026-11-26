import Bilevel.ChiCarrierSourceNode
import Bilevel.ChiRecursiveSourceGeometry

/-! Source floor-length estimates and monotone physical widths establish
the coarser-scale condition for every actual ancestor selector. -/
noncomputable section
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

theorem source_width_sqrt_length_le_parent {cn η hp r : ℝ}
    (hcn : 0<cn) (hcn1 : cn≤1) (hη : 0<η) (hhp : 0<hp) (hr : 1≤r)
    (hlen : 128≤cn/η^2) :
    (η*hp/r)*Real.sqrt (((sourceChainIndex cn r η:ℕ):ℝ)+1)≤hp := by
  have hr0 : 0<r := by linarith
  have hs := scaled_sqrt_chain_length hcn.le hr0.le hη _ (sourceChainIndex_length hcn hr hη hlen).2
  have hsc : Real.sqrt cn≤1 := Real.sqrt_le_one.mpr hcn1
  have hsr : Real.sqrt r≤r := by
    have hsqr := Real.sq_sqrt hr0.le
    have hsr1 : 1≤Real.sqrt r := Real.one_le_sqrt.mpr hr
    nlinarith
  have hsprod : Real.sqrt cn*Real.sqrt r≤r :=
    (mul_le_mul_of_nonneg_right hsc (Real.sqrt_nonneg r)).trans (by simpa only [one_mul] using hsr)
  have hh := mul_le_mul_of_nonneg_left (hs.trans hsprod) hhp.le
  calc
    _ = (hp*(η*Real.sqrt (((sourceChainIndex cn r η:ℕ):ℝ)+1)))/r := by ring
    _ ≤ hp := (div_le_iff₀ hr0).mpr hh

theorem parentScale_width_antitone (initial : Scale) (r η : ℕ → ℝ)
    (hl : 0 < initial.curvature) (hw : 0 < initial.width)
    (hr : ∀ j,1≤r j) (hη : ∀ j,0<η j) (hη1 : ∀ j,η j≤1) :
    Antitone (fun j => (parentScale initial r η j).width) := by
  apply antitone_nat_of_succ_le
  intro j
  have hp := (parentScale_positive initial r η hl hw hr hη j).2
  have hr0 : 0<r j := by linarith [hr j]
  change η j*(parentScale initial r η j).width/r j≤(parentScale initial r η j).width
  apply (div_le_iff₀ hr0).mpr
  nlinarith only [mul_le_mul_of_nonneg_right ((hη1 j).trans (hr j)) hp.le]

theorem source_geometry_ancestor_width
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (initial : Scale) (r η b : ℕ → ℝ) (A K ζ cn CR : ℝ)
    (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F)
    (hl : 0 < initial.curvature) (hw : 0 < initial.width) (hr : ∀ j,1≤r j)
    (hη : ∀ j,0<η j) (hη1 : ∀ j,η j≤1) (hcn : 0<cn) (hcn1 : cn≤1)
    (hlen : ∀ j,128≤cn/(η j)^2) (j k : ℕ) (hjk : j<k) (I P : List ℕ) :
    let D := sourceGeometry initial r η b A K ζ cn CR U
    (D k P).width*Real.sqrt (((D k P).n:ℝ)+1)≤(D j I).width := by
  dsimp only
  have hp := parentScale_positive initial r η hl hw hr hη
  have hs := source_width_sqrt_length_le_parent hcn hcn1 (hη k) (hp k).2 (hr k) (hlen k)
  have hm := parentScale_width_antitone initial r η hl hw hr hη hη1 (by omega : j+1≤k)
  exact hs.trans hm

end Bilevel.ChiCarrier
