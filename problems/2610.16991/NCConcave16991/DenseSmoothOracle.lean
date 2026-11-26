import NCConcave16991.DenseSmoothProblem
import NCConcave16991.DenseSmoothLocality

/-! # Exact actual-oracle replies from past directions and one frontier row -/

noncomputable section

namespace NCConcave16991.DenseSmooth

open Set
open scoped BigOperators InnerProductSpace ContDiff

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 4
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n T : ℕ}

theorem truncatedChain_contDiff (h : ℕ) (ρ : ℝ) (u : Fin (T + 1) → E)
    (rows : Fin n → Fin (T + 1) → E) (i : Fin n) :
    ContDiff ℝ ∞ (truncatedChain h ρ u rows i) := by
  have hl (j : Fin T) : ContDiff ℝ ∞ (fun x : Blocks E T ↦ if j.val < h then link ρ u rows i j x else 0) := by
    by_cases hj : j.val < h
    · simpa only [hj, ite_true] using link_contDiff ρ u rows i j
    · simpa only [hj, ite_false] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Blocks E T ↦ (0 : ℝ)))
  exact (((contDiff_const.mul (coordinate_contDiff (rows i) 0)).neg).sub
    (ContDiff.sum (fun j _ ↦ hl j))).add (contDiff_const.mul (contDiff_norm_sq ℝ))

variable [FiniteDimensional ℝ E]

def flatTruncated (h : ℕ) (ρ : ℝ) (u : Fin (T + 1) → E)
    (rows : Fin n → Fin (T + 1) → E) (i : Fin n) (x : PrimalSpace (primalDimension E T)) : ℝ :=
  truncatedChain h ρ u rows i ((primalCoordinates E T).symm x)

theorem flat_firstJet_eq_reference (h : ℕ) (ρ : ℝ) (A : Table E n T ρ)
    (u : Fin (T + 1) → E) (rows : Fin n → Fin (T + 1) → E) (i : Fin n)
    (x : PrimalSpace (primalDimension E T))
    (hu : ∀ j, j.val < h → A.direction j = u j)
    (hr : ∀ j, j.val ≤ h → A.row i j = rows i j)
    (hflat : ∀ j : Fin T, h ≤ j.val →
      coordinate A.direction ((primalCoordinates E T).symm x) j.castSucc ≤ 5 / 32) :
    flatComponent ρ A.direction A.row i x = flatTruncated h ρ u rows i x ∧
      gradient (flatComponent ρ A.direction A.row i) x = gradient (flatTruncated h ρ u rows i) x := by
  let z := (primalCoordinates E T).symm x
  have hj := component_firstJet_eq_truncated h ρ A.direction A.row i z hflat
  have he := truncatedChain_eq_of_known_data h ρ A.direction u A.row rows i hu hr
  have hd : fderiv ℝ (componentChain ρ A.direction A.row i) z =
      fderiv ℝ (truncatedChain h ρ u rows i) z := by
    have hh := congrArg (InnerProductSpace.toDual ℝ (Blocks E T)) hj.2
    simp only [toDual_gradient] at hh
    rw [he] at hh
    exact hh
  constructor
  · change componentChain ρ A.direction A.row i z = truncatedChain h ρ u rows i z
    exact hj.1.trans (congrFun he z)
  · apply (InnerProductSpace.toDual ℝ (PrimalSpace (primalDimension E T))).injective
    rw [toDual_gradient, toDual_gradient]
    have hf := (((componentChain_contDiff ρ A.direction A.row i).differentiable (by simp) z).hasFDerivAt.comp x
      (primalCoordinates E T).symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
    have hg := (((truncatedChain_contDiff h ρ u rows i).differentiable (by simp) z).hasFDerivAt.comp x
      (primalCoordinates E T).symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
    change fderiv ℝ (fun y ↦ componentChain ρ A.direction A.row i ((primalCoordinates E T).symm y)) x =
      fderiv ℝ (fun y ↦ truncatedChain h ρ u rows i ((primalCoordinates E T).symm y)) x
    rw [hd] at hf
    convert hf.trans hg.symm using 1 <;> rfl

def referenceReply (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) (h : ℕ)
    (u : Fin (T + 1) → E) (rows : Fin n → Fin (T + 1) → E)
    (o : OracleQuery n (primalDimension E T) (smoothDualDomain (parameters hn hρ T))) :
    OracleAnswer (primalDimension E T) 0 :=
  (flatTruncated h ρ u rows o.1 o.2.1, gradient (flatTruncated h ρ u rows o.1) o.2.1, 0)

theorem oracleResponse_eq_reference (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (A : Table E n T ρ) (h : ℕ) (u : Fin (T + 1) → E) (rows : Fin n → Fin (T + 1) → E)
    (o : OracleQuery n (primalDimension E T) (smoothDualDomain (parameters hn hρ T)))
    (hu : ∀ j, j.val < h → A.direction j = u j)
    (hr : ∀ j, j.val ≤ h → A.row o.1 j = rows o.1 j)
    (hflat : ∀ j : Fin T, h ≤ j.val →
      coordinate A.direction ((primalCoordinates E T).symm o.2.1) j.castSucc ≤ 5 / 32) :
    oracleResponse (finiteSum hn hρ hρ1 A).toProblem o = referenceReply hn hρ h u rows o := by
  have hh := flat_firstJet_eq_reference h ρ A u rows o.1 o.2.1 hu hr hflat
  change (flatComponent ρ A.direction A.row o.1 o.2.1,
    gradient (flatComponent ρ A.direction A.row o.1) o.2.1, (0 : DualSpace 0)) = _
  rw [hh.1, hh.2]
  rfl

end NCConcave16991.DenseSmooth
