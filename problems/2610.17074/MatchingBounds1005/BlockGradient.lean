import MatchingBounds1005.BlockCertificate
import MatchingBounds1005.Primitive
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Derivatives of the actual smooth block objective

The finite product is initially equipped with its standard norm for Fréchet
differentiation. Derivative functionals and block coordinate gradients are
identified explicitly; Euclidean gradient estimates are kept separate from
the product-norm operator norm.
-/

noncomputable section
open scoped InnerProductSpace BigOperators

namespace MatchingBounds1005.BlockGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

/-- Dependence of the chain on one block, holding both neighbors fixed. -/
def sectionEnergy (r uPrev vNext : ℝ) (z : E) : ℝ :=
  G.quadraticBlock uPrev z + G.tau * Primitive.potential r ⟪G.a, z⟫_ℝ -
    G.lam * vNext * ⟪G.a, z⟫_ℝ

theorem sectionEnergy_hasFDerivAt (r uPrev vNext : ℝ) (z : E) :
    HasFDerivAt (G.sectionEnergy r uPrev vNext)
      (innerSL ℝ (G.gradientBlock (Primitive.slope r) uPrev z vNext)) z := by
  let Hc : E →L[ℝ] E := LinearMap.toContinuousLinearMap G.H
  have hid := hasFDerivAt_id (𝕜 := ℝ) z
  have hH := Hc.hasFDerivAt (x := z)
  have ha := (innerSL ℝ G.a).hasFDerivAt (x := z)
  have he := (innerSL ℝ G.e).hasFDerivAt (x := z)
  have hp := (Primitive.potential_hasDerivAt r ⟪G.a, z⟫_ℝ).comp_hasFDerivAt z ha
  have h := ((((hid.inner ℝ hH).const_mul (1 / 2 : ℝ)).sub
      (he.const_mul (G.lam * uPrev))).add
      ((ha.mul ha).const_mul (G.kappa / 2))) |>.add (hp.const_mul G.tau)
  have h' := h.sub (ha.const_mul (G.lam * vNext))
  convert h' using 1
  · funext y
    simp only [sectionEnergy, quadraticBlock, Hc, LinearMap.coe_toContinuousLinearMap',
      innerSL_apply, id_eq, Function.comp_apply]
    ring
  · ext v
    simp only [gradientBlock, innerSL_apply, inner_add_left, inner_sub_left,
      real_inner_smul_left, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      fderivInnerCLM_apply, smul_eq_mul, Hc, LinearMap.coe_toContinuousLinearMap', id_eq]
    rw [G.symmetric z v]
    rw [real_inner_comm (G.H z) v]
    ring

def localEnergy (r : ℝ) : E → ℝ := G.sectionEnergy r 0 0

def localGradient (r : ℝ) (z : E) : E := G.gradientBlock (Primitive.slope r) 0 z 0

theorem localEnergy_hasFDerivAt (r : ℝ) (z : E) :
    HasFDerivAt (G.localEnergy r) (innerSL ℝ (G.localGradient r z)) z :=
  G.sectionEnergy_hasFDerivAt r 0 0 z

/-- Readout of a single block as a continuous linear functional. -/
def readoutCLM {n : ℕ} (a : E) (i : Fin (n + 1)) :
    (Fin (n + 1) → E) →L[ℝ] ℝ :=
  (innerSL ℝ a).comp (ContinuousLinearMap.proj i)

@[simp] theorem readoutCLM_apply {n : ℕ} (a : E) (i : Fin (n + 1))
    (z : Fin (n + 1) → E) : readoutCLM a i z = ⟪a, z i⟫_ℝ := rfl

/-- The manuscript's objective with `n+1` blocks, written as local terms and
the `n` adjacent couplings. The first input readout is exactly one. -/
def objective (r : ℝ) (n : ℕ) (z : Fin (n + 1) → E) : ℝ :=
  (∑ i, G.localEnergy r (z i)) - G.lam * ⟪G.e, z 0⟫_ℝ -
    G.lam * ∑ i : Fin n, ⟪G.a, z i.castSucc⟫_ℝ * ⟪G.e, z i.succ⟫_ℝ

def objectiveDerivative (r : ℝ) (n : ℕ) (z : Fin (n + 1) → E) :
    (Fin (n + 1) → E) →L[ℝ] ℝ :=
  (∑ i, (innerSL ℝ (G.localGradient r (z i))).comp (ContinuousLinearMap.proj i)) -
    G.lam • readoutCLM G.e 0 -
    G.lam • ∑ i : Fin n,
      (⟪G.e, z i.succ⟫_ℝ • readoutCLM G.a i.castSucc +
        ⟪G.a, z i.castSucc⟫_ℝ • readoutCLM G.e i.succ)

/-- Full Fréchet derivative of the actual finite-chain potential. -/
theorem objective_hasFDerivAt (r : ℝ) (n : ℕ) (z : Fin (n + 1) → E) :
    HasFDerivAt (G.objective r n) (G.objectiveDerivative r n z) z := by
  have hl : ∀ i : Fin (n + 1), HasFDerivAt (fun y : Fin (n + 1) → E => G.localEnergy r (y i))
      ((innerSL ℝ (G.localGradient r (z i))).comp (ContinuousLinearMap.proj i)) z := by
    intro i
    exact (G.localEnergy_hasFDerivAt r (z i)).comp z
      (ContinuousLinearMap.proj i : (Fin (n + 1) → E) →L[ℝ] E).hasFDerivAt
  have he := (readoutCLM G.e (0 : Fin (n + 1))).hasFDerivAt (x := z)
  have hc : ∀ i : Fin n,
      HasFDerivAt (fun y : Fin (n + 1) → E => ⟪G.a, y i.castSucc⟫_ℝ * ⟪G.e, y i.succ⟫_ℝ)
        (⟪G.e, z i.succ⟫_ℝ • readoutCLM G.a i.castSucc +
          ⟪G.a, z i.castSucc⟫_ℝ • readoutCLM G.e i.succ) z := by
    intro i
    have h := (readoutCLM G.a i.castSucc).hasFDerivAt (x := z) |>.mul
      (readoutCLM G.e i.succ).hasFDerivAt
    simpa only [readoutCLM_apply, add_comm] using h
  exact ((HasFDerivAt.sum (u := Finset.univ) (fun i _ => hl i)).sub
    (he.const_mul G.lam)).sub
    ((HasFDerivAt.sum (u := Finset.univ) (fun i _ => hc i)).const_mul G.lam)

theorem objective_fderiv (r : ℝ) (n : ℕ) (z : Fin (n + 1) → E) :
    fderiv ℝ (G.objective r n) z = G.objectiveDerivative r n z :=
  (G.objective_hasFDerivAt r n z).fderiv

def incomingReadout {n : ℕ} (z : Fin (n + 1) → E) (i : Fin (n + 1)) : ℝ :=
  (if i = 0 then 1 else 0) +
    ∑ j : Fin n, if j.succ = i then ⟪G.a, z j.castSucc⟫_ℝ else 0

def outgoingEntry {n : ℕ} (z : Fin (n + 1) → E) (i : Fin (n + 1)) : ℝ :=
  ∑ j : Fin n, if j.castSucc = i then ⟪G.e, z j.succ⟫_ℝ else 0

@[simp] theorem incomingReadout_zero {n : ℕ} (z : Fin (n + 1) → E) :
    G.incomingReadout z 0 = 1 := by simp [incomingReadout]

@[simp] theorem incomingReadout_succ {n : ℕ} (z : Fin (n + 1) → E) (i : Fin n) :
    G.incomingReadout z i.succ = ⟪G.a, z i.castSucc⟫_ℝ := by simp [incomingReadout]

@[simp] theorem outgoingEntry_castSucc {n : ℕ} (z : Fin (n + 1) → E) (i : Fin n) :
    G.outgoingEntry z i.castSucc = ⟪G.e, z i.succ⟫_ℝ := by simp [outgoingEntry]

@[simp] theorem outgoingEntry_last {n : ℕ} (z : Fin (n + 1) → E) :
    G.outgoingEntry z (Fin.last n) = 0 := by simp [outgoingEntry, Fin.castSucc_ne_last]

/-- The actual coordinate-gradient vector, including both boundary conventions. -/
def objectiveGradient (r : ℝ) (n : ℕ) (z : Fin (n + 1) → E) (i : Fin (n + 1)) : E :=
  G.gradientBlock (Primitive.slope r) (G.incomingReadout z i) (z i) (G.outgoingEntry z i)

theorem objectiveDerivative_single (r : ℝ) (n : ℕ) (z : Fin (n + 1) → E)
    (i : Fin (n + 1)) (v : E) :
    G.objectiveDerivative r n z (Pi.single i v) = ⟪G.objectiveGradient r n z i, v⟫_ℝ := by
  have hlocal : (∑ j : Fin (n + 1), ⟪G.localGradient r (z j), (Pi.single i v : Fin (n + 1) → E) j⟫_ℝ) =
      ⟪G.localGradient r (z i), v⟫_ℝ := by
    rw [Fintype.sum_eq_single i]
    · simp
    · intro j hj
      simp [Pi.single_eq_of_ne hj]
  have hfirst : ⟪G.e, (Pi.single i v : Fin (n + 1) → E) 0⟫_ℝ =
      (if i = 0 then 1 else 0) * ⟪G.e, v⟫_ℝ := by
    by_cases hi : i = 0
    · subst i
      simp
    · simp [hi, Pi.single_eq_of_ne (Ne.symm hi)]
  have hout : (∑ j : Fin n, ⟪G.e, z j.succ⟫_ℝ * ⟪G.a, (Pi.single i v : Fin (n + 1) → E) j.castSucc⟫_ℝ) =
      G.outgoingEntry z i * ⟪G.a, v⟫_ℝ := by
    rw [outgoingEntry, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.castSucc = i
    · subst i
      simp
    · simp [hj, Pi.single_eq_of_ne hj]
  have hin : (∑ j : Fin n, ⟪G.a, z j.castSucc⟫_ℝ * ⟪G.e, (Pi.single i v : Fin (n + 1) → E) j.succ⟫_ℝ) =
      (∑ j : Fin n, if j.succ = i then ⟪G.a, z j.castSucc⟫_ℝ else 0) * ⟪G.e, v⟫_ℝ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.succ = i
    · subst i
      simp
    · simp [hj, Pi.single_eq_of_ne hj]
  simp only [objectiveDerivative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, innerSL_apply, readoutCLM_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, hlocal, hfirst, hout, hin]
  simp only [objectiveGradient, localGradient, gradientBlock, incomingReadout,
    inner_add_left, inner_sub_left, real_inner_smul_left]
  ring

/-- The computed block vector is the coordinate derivative of the actual F. -/
theorem objective_fderiv_single (r : ℝ) (n : ℕ) (z : Fin (n + 1) → E)
    (i : Fin (n + 1)) (v : E) :
    fderiv ℝ (G.objective r n) z (Pi.single i v) = ⟪G.objectiveGradient r n z i, v⟫_ℝ := by
  rw [G.objective_fderiv, G.objectiveDerivative_single]

end MatchingBounds1005.BlockGeometry
