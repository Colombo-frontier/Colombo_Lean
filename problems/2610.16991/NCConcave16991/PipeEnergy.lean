import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Actual path matrices and quadratic elimination (Appendix E.11--E.12)

The finite path matrix is constructed as `μ I + Bᵀ B`, where the actual
incidence matrix `B` takes adjacent differences. Its sum-of-squares identity,
positive definiteness and invertibility are proved. The quadratic elimination
theorems use the actual matrix inverse and prove the maximizing energy by
completing the square. No endpoint Green formula is assumed in these results.

The branching innovation-space decomposition, hyperbolic closed form and its
uniform endpoint constants are separate tasks; they are not claimed here.
-/

namespace NCConcave16991
namespace PipeEnergy

open Matrix
open scoped BigOperators Matrix

/-- The oriented incidence matrix of a path with `m` edges and `m+1` vertices. -/
def incidence (m : ℕ) : Matrix (Fin m) (Fin (m + 1)) ℝ :=
  fun e => Pi.single e.succ 1 - Pi.single e.castSucc 1

theorem incidence_mulVec (m : ℕ) (w : Fin (m + 1) → ℝ) (e : Fin m) :
    (incidence m *ᵥ w) e = w e.succ - w e.castSucc := by
  change (Pi.single e.succ (1 : ℝ) - Pi.single e.castSucc 1) ⬝ᵥ w = _
  rw [sub_dotProduct]
  simp

/-- The Neumann path Laplacian, without any mass shift. -/
def pathLaplacian (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  (incidence m)ᵀ * incidence m

noncomputable def massPath (m : ℕ) (μ : ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  μ • 1 + pathLaplacian m

theorem pathLaplacian_posSemidef (m : ℕ) : (pathLaplacian m).PosSemidef := by
  simpa [pathLaplacian] using Matrix.posSemidef_conjTranspose_mul_self (incidence m)

theorem massPath_posDef (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    (massPath m μ).PosDef := by
  exact (Matrix.PosDef.one.smul hμ).add_posSemidef (pathLaplacian_posSemidef m)

/-- Invertibility follows from positivity of the actual constructed matrix. -/
theorem massPath_isUnit (m : ℕ) {μ : ℝ} (hμ : 0 < μ) : IsUnit (massPath m μ) :=
  (massPath_posDef m hμ).isUnit

/-- Exact sum-of-squares form of the paper's scalar path operator. -/
theorem massPath_quadratic (m : ℕ) (μ : ℝ) (w : Fin (m + 1) → ℝ) :
    w ⬝ᵥ (massPath m μ *ᵥ w) =
      μ * (∑ j, (w j) ^ 2) + ∑ e : Fin m, (w e.succ - w e.castSucc) ^ 2 := by
  unfold massPath pathLaplacian
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, incidence_mulVec, pow_two, smul_eq_mul]

theorem massPath_quadratic_lower_bound (m : ℕ) (μ : ℝ) (w : Fin (m + 1) → ℝ) :
    μ * (∑ j, (w j) ^ 2) ≤ w ⬝ᵥ (massPath m μ *ᵥ w) := by
  rw [massPath_quadratic]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Constant vectors have no path energy; the mass lower bound is attained. -/
theorem massPath_constant (m : ℕ) (μ t : ℝ) :
    massPath m μ *ᵥ (fun _ => t) = fun _ => μ * t := by
  have hd : incidence m *ᵥ (fun _ => t) = 0 := by
    ext e
    simp [incidence_mulVec]
  simp only [massPath, pathLaplacian, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hd, Matrix.mulVec_zero, add_zero]
  rfl

/-- The incidence adjoint at the left endpoint. -/
theorem incidence_transpose_zero (m : ℕ) (y : Fin (m + 1) → ℝ) :
    ((incidence (m + 1))ᵀ *ᵥ y) 0 = -y 0 := by
  have hrow : (fun e => incidence (m + 1) e (0 : Fin (m + 2))) =
      -Pi.single (0 : Fin (m + 1)) (1 : ℝ) := by
    funext e
    by_cases he : e = 0
    · subst e
      simp [incidence]
    · have hec : e.castSucc ≠ (0 : Fin (m + 2)) := by
        intro h
        apply he
        apply Fin.ext
        exact congrArg (fun v : Fin (m + 2) => v.val) h
      simp [incidence, he, hec]
  change (fun e => incidence (m + 1) e (0 : Fin (m + 2))) ⬝ᵥ y = _
  rw [hrow, neg_dotProduct]
  simp

/-- The incidence adjoint at the right endpoint. -/
theorem incidence_transpose_last (m : ℕ) (y : Fin (m + 1) → ℝ) :
    ((incidence (m + 1))ᵀ *ᵥ y) (Fin.last (m + 1)) = y (Fin.last m) := by
  have hrow : (fun e => incidence (m + 1) e (Fin.last (m + 1))) =
      Pi.single (Fin.last m) (1 : ℝ) := by
    funext e
    have hs : Fin.last (m + 1) = e.succ ↔ e = Fin.last m := by
      simp only [Fin.ext_iff, Fin.val_last, Fin.val_succ]
      omega
    simp [incidence, Pi.single_apply, hs, Fin.castSucc_ne_last]
  change (fun e => incidence (m + 1) e (Fin.last (m + 1))) ⬝ᵥ y = _
  rw [hrow]
  simp

/-- The incidence adjoint at every interior vertex: incoming minus outgoing
edge flow. -/
theorem incidence_transpose_interior (m : ℕ) (j : Fin (m + 1))
    (y : Fin (m + 2) → ℝ) :
    ((incidence (m + 2))ᵀ *ᵥ y) j.succ.castSucc = y j.castSucc - y j.succ := by
  have hrow : (fun e => incidence (m + 2) e j.castSucc.succ) =
      Pi.single j.castSucc (1 : ℝ) - Pi.single j.succ 1 := by
    funext e
    have hs : j.castSucc.succ = e.succ ↔ e = j.castSucc := by
      simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
      omega
    have hc : j.castSucc.succ = e.castSucc ↔ e = j.succ := by
      simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
      omega
    simp [incidence, Pi.single_apply, hs, hc]
  change (fun e => incidence (m + 2) e j.castSucc.succ) ⬝ᵥ y = _
  rw [hrow, sub_dotProduct]
  simp

/-- Actual first row of the massive Neumann tridiagonal operator. -/
theorem massPath_root_recurrence (m : ℕ) (μ : ℝ) (w : Fin (m + 2) → ℝ) :
    (massPath (m + 1) μ *ᵥ w) 0 =
      (μ + 1) * w 0 - w (0 : Fin (m + 1)).succ := by
  simp only [massPath, pathLaplacian, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, incidence_transpose_zero, incidence_mulVec, Fin.castSucc_zero]
  ring

/-- Actual last row of the massive Neumann tridiagonal operator. -/
theorem massPath_last_recurrence (m : ℕ) (μ : ℝ) (w : Fin (m + 2) → ℝ) :
    (massPath (m + 1) μ *ᵥ w) (Fin.last (m + 1)) =
      (μ + 1) * w (Fin.last (m + 1)) - w (Fin.last m).castSucc := by
  simp only [massPath, pathLaplacian, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, incidence_transpose_last, incidence_mulVec, Fin.succ_last]
  ring

/-- Actual interior row, with diagonal `μ+2` and adjacent entries `-1`. -/
theorem massPath_interior_recurrence (m : ℕ) (μ : ℝ) (j : Fin (m + 1))
    (w : Fin (m + 3) → ℝ) :
    (massPath (m + 2) μ *ᵥ w) j.succ.castSucc =
      (μ + 2) * w j.succ.castSucc - w j.castSucc.castSucc - w j.succ.succ := by
  have he : j.castSucc.succ = j.succ.castSucc := by apply Fin.ext; rfl
  simp only [massPath, pathLaplacian, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, incidence_transpose_interior, incidence_mulVec, he]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unnormalized dual quadratic, including its linear source term. -/
noncomputable def saddle (M : Matrix ι ι ℝ) (h w : ι → ℝ) : ℝ :=
  h ⬝ᵥ w - (1 / 2 : ℝ) * (w ⬝ᵥ (M *ᵥ w))

noncomputable def optimizer (M : Matrix ι ι ℝ) (h : ι → ℝ) : ι → ℝ :=
  M⁻¹ *ᵥ h

theorem optimizer_equation {M : Matrix ι ι ℝ} (hM : M.PosDef) (h : ι → ℝ) :
    M *ᵥ optimizer M h = h := by
  let _ := hM.isUnit.invertible
  simp only [optimizer, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- Exact completing-square identity with the actual inverse-based optimizer. -/
theorem saddle_complete_square {M : Matrix ι ι ℝ} (hM : M.PosDef) (h w : ι → ℝ) :
    saddle M h w =
      (1 / 2 : ℝ) * (h ⬝ᵥ optimizer M h) -
        (1 / 2 : ℝ) * ((w - optimizer M h) ⬝ᵥ (M *ᵥ (w - optimizer M h))) := by
  have hs : optimizer M h ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (M *ᵥ optimizer M h) := by
    simpa using hM.isHermitian.star_dotProduct_mulVec_comm (optimizer M h) w
  have he := optimizer_equation hM h
  simp only [saddle, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, hs, he]
  rw [dotProduct_comm w h, dotProduct_comm (optimizer M h) h]
  ring

theorem saddle_at_optimizer {M : Matrix ι ι ℝ} (hM : M.PosDef) (h : ι → ℝ) :
    saddle M h (optimizer M h) = (1 / 2 : ℝ) * (h ⬝ᵥ optimizer M h) := by
  simp [saddle_complete_square hM]

theorem saddle_le_maximum {M : Matrix ι ι ℝ} (hM : M.PosDef) (h w : ι → ℝ) :
    saddle M h w ≤ (1 / 2 : ℝ) * (h ⬝ᵥ optimizer M h) := by
  rw [saddle_complete_square hM]
  have hn : 0 ≤ (w - optimizer M h) ⬝ᵥ (M *ᵥ (w - optimizer M h)) := by
    simpa using hM.posSemidef.dotProduct_mulVec_nonneg (w - optimizer M h)
  linarith

/-- The energy is an attained greatest value, not an assumed formal formula. -/
theorem saddle_isGreatest {M : Matrix ι ι ℝ} (hM : M.PosDef) (h : ι → ℝ) :
    IsGreatest (Set.range (saddle M h)) ((1 / 2 : ℝ) * (h ⬝ᵥ optimizer M h)) := by
  refine ⟨⟨optimizer M h, saddle_at_optimizer hM h⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact saddle_le_maximum hM h w

theorem saddle_maximizer_unique {M : Matrix ι ι ℝ} (hM : M.PosDef) (h w : ι → ℝ)
    (hw : saddle M h w = (1 / 2 : ℝ) * (h ⬝ᵥ optimizer M h)) :
    w = optimizer M h := by
  by_contra hne
  have hdiff : w - optimizer M h ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < (w - optimizer M h) ⬝ᵥ (M *ᵥ (w - optimizer M h)) := by
    simpa using hM.dotProduct_mulVec_pos hdiff
  have hid := saddle_complete_square hM h w
  linarith

/-- Elimination of a genuine path dual quadratic, as an immediate application
of its proved positive definiteness and the completing-square theorem. -/
theorem path_saddle_isGreatest (m : ℕ) {μ : ℝ} (hμ : 0 < μ)
    (h : Fin (m + 1) → ℝ) :
    IsGreatest (Set.range (saddle (massPath m μ) h))
      ((1 / 2 : ℝ) * (h ⬝ᵥ ((massPath m μ)⁻¹ *ᵥ h))) :=
  saddle_isGreatest (massPath_posDef m hμ) h

/-- Scalar scaling of the actual maximizing vector. -/
theorem optimizer_scaled {M : Matrix ι ι ℝ} (hM : M.PosDef)
    {β : ℝ} (hβ : 0 < β) (r : ℝ) (h : ι → ℝ) :
    optimizer (β • M) (r • h) = (r / β) • optimizer M h := by
  have hβM := hM.smul hβ
  apply Matrix.mulVec_injective_of_isUnit hβM.isUnit
  rw [optimizer_equation hβM, Matrix.smul_mulVec, Matrix.mulVec_smul,
    optimizer_equation hM, smul_smul]
  have hs : β * (r / β) = r := by field_simp
  rw [hs]

/-- Exact energy of a linearly coupled, scaled positive-definite dual
quadratic, including the paper's `r` and `β` normalization. -/
theorem scaled_saddle_isGreatest {M : Matrix ι ι ℝ} (hM : M.PosDef)
    {β : ℝ} (hβ : 0 < β) (r : ℝ) (h : ι → ℝ) :
    IsGreatest (Set.range (fun w =>
      r * (h ⬝ᵥ w) - β / 2 * (w ⬝ᵥ (M *ᵥ w))))
      (r ^ 2 / (2 * β) * (h ⬝ᵥ optimizer M h)) := by
  have he : (fun w => r * (h ⬝ᵥ w) - β / 2 * (w ⬝ᵥ (M *ᵥ w))) =
      saddle (β • M) (r • h) := by
    funext w
    simp only [saddle, Matrix.smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have henergy : (1 / 2 : ℝ) * ((r • h) ⬝ᵥ optimizer (β • M) (r • h)) =
      r ^ 2 / (2 * β) * (h ⬝ᵥ optimizer M h) := by
    rw [optimizer_scaled hM hβ]
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  rw [he, ← henergy]
  exact saddle_isGreatest (hM.smul hβ) (r • h)

/-- The exact terminal-source Green column of the actual massive path. -/
noncomputable def terminalGreen (m : ℕ) (μ : ℝ) : Fin (m + 2) → ℝ :=
  optimizer (massPath (m + 1) μ) (Pi.single (Fin.last (m + 1)) 1)

/-- The inverse column satisfies the Neumann root equation. -/
theorem terminalGreen_root (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    (μ + 1) * terminalGreen m μ 0 -
      terminalGreen m μ (0 : Fin (m + 1)).succ = 0 := by
  have he := congrArg (fun v : Fin (m + 2) → ℝ => v 0)
    (optimizer_equation (massPath_posDef (m + 1) hμ)
      (Pi.single (Fin.last (m + 1)) 1))
  change (massPath (m + 1) μ *ᵥ terminalGreen m μ) 0 = _ at he
  rw [massPath_root_recurrence] at he
  have hne : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    simp [Fin.ext_iff]
  simpa [Pi.single_apply, hne] using he

/-- The inverse column satisfies the unit-forced terminal equation. -/
theorem terminalGreen_last (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    (μ + 1) * terminalGreen m μ (Fin.last (m + 1)) -
      terminalGreen m μ (Fin.last m).castSucc = 1 := by
  have he := congrArg (fun v : Fin (m + 2) → ℝ => v (Fin.last (m + 1)))
    (optimizer_equation (massPath_posDef (m + 1) hμ)
      (Pi.single (Fin.last (m + 1)) 1))
  change (massPath (m + 1) μ *ᵥ terminalGreen m μ) (Fin.last (m + 1)) = _ at he
  rw [massPath_last_recurrence] at he
  simpa using he

/-- The inverse column satisfies the homogeneous interior recurrence. -/
theorem terminalGreen_interior (m : ℕ) {μ : ℝ} (hμ : 0 < μ) (j : Fin (m + 1)) :
    (μ + 2) * terminalGreen (m + 1) μ j.succ.castSucc -
      terminalGreen (m + 1) μ j.castSucc.castSucc -
      terminalGreen (m + 1) μ j.succ.succ = 0 := by
  have he := congrArg (fun v : Fin (m + 3) → ℝ => v j.succ.castSucc)
    (optimizer_equation (massPath_posDef (m + 2) hμ)
      (Pi.single (Fin.last (m + 2)) 1))
  change (massPath (m + 2) μ *ᵥ terminalGreen (m + 1) μ) j.succ.castSucc = _ at he
  rw [massPath_interior_recurrence] at he
  simpa [Pi.single_apply, Fin.castSucc_ne_last] using he

/-- The total mass of the actual inverse column is determined exactly by the
constant-vector eigenfunction, without assuming a closed form. -/
theorem terminalGreen_mass_sum (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    μ * (∑ j, terminalGreen m μ j) = 1 := by
  have hM := massPath_posDef (m + 1) hμ
  have he : massPath (m + 1) μ *ᵥ terminalGreen m μ =
      Pi.single (Fin.last (m + 1)) 1 := optimizer_equation hM _
  have hs : (fun _ : Fin (m + 2) => (1 : ℝ)) ⬝ᵥ
      (massPath (m + 1) μ *ᵥ terminalGreen m μ) =
      terminalGreen m μ ⬝ᵥ (massPath (m + 1) μ *ᵥ (fun _ => 1)) := by
    simpa using hM.isHermitian.star_dotProduct_mulVec_comm
      (fun _ => 1) (terminalGreen m μ)
  rw [he, massPath_constant] at hs
  simp [dotProduct] at hs
  calc
    μ * (∑ j, terminalGreen m μ j) = ∑ j, μ * terminalGreen m μ j := Finset.mul_sum ..
    _ = 1 := by simpa only [mul_comm] using hs.symm

theorem terminalGreen_sum (m : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    (∑ j, terminalGreen m μ j) = 1 / μ := by
  apply (eq_div_iff hμ.ne').mpr
  simpa only [mul_comm] using terminalGreen_mass_sum m hμ

/-- At the paper's mass `N⁻²`, with `N=m+2`, the actual column sums to `N²`. -/
theorem terminalGreen_sum_normalized (m : ℕ) :
    (∑ j, terminalGreen m (1 / ((m : ℝ) + 2) ^ 2) j) = ((m : ℝ) + 2) ^ 2 := by
  have hμ : 0 < 1 / ((m : ℝ) + 2) ^ 2 := by positivity
  simpa only [one_div_one_div] using terminalGreen_sum m hμ

/-- The actual injection of the two scalar connectors into the two path ends. -/
def endpointInjection (m : ℕ) : Matrix (Fin (m + 2)) (Fin 2) ℝ :=
  fun v j => if j = 0 then (if v = 0 then 1 else 0)
    else (if v = Fin.last (m + 1) then -1 else 0)

theorem endpointInjection_mulVec (m : ℕ) (v : Fin 2 → ℝ) :
    endpointInjection m *ᵥ v =
      Pi.single 0 (v 0) - Pi.single (Fin.last (m + 1)) (v 1) := by
  ext j
  simp [endpointInjection, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
  split_ifs <;> ring

/-- The actual eliminated connector energy, before evaluating any Green
entries. The inverse in this definition is the genuine finite matrix inverse. -/
noncomputable def connectorEnergy {κ : Type*} [Fintype κ]
    (M : Matrix ι ι ℝ) (C : Matrix ι κ ℝ) (d : ℝ) (v : κ → ℝ) : ℝ :=
  d * (v ⬝ᵥ v) + (1 / 2 : ℝ) * ((C *ᵥ v) ⬝ᵥ optimizer M (C *ᵥ v))

theorem connectorEnergy_isGreatest {κ : Type*} [Fintype κ]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) (C : Matrix ι κ ℝ) (d : ℝ) (v : κ → ℝ) :
    IsGreatest (Set.range (fun w => d * (v ⬝ᵥ v) + saddle M (C *ᵥ v) w))
      (connectorEnergy M C d v) := by
  refine ⟨⟨optimizer M (C *ᵥ v), ?_⟩, ?_⟩
  · simp only [connectorEnergy, saddle_at_optimizer hM]
  · rintro _ ⟨w, rfl⟩
    dsimp [connectorEnergy]
    linarith [saddle_le_maximum hM (C *ᵥ v) w]

/-- The curvature identity for the eliminated function itself. Cross terms
cancel by linearity; no desired endpoint energy formula is an assumption. -/
theorem connectorEnergy_second_difference {κ : Type*} [Fintype κ]
    (M : Matrix ι ι ℝ) (C : Matrix ι κ ℝ) (d : ℝ) (v h : κ → ℝ) :
    connectorEnergy M C d (v + h) + connectorEnergy M C d (v - h) -
      2 * connectorEnergy M C d v =
      (2 * d) * (h ⬝ᵥ h) + (C *ᵥ h) ⬝ᵥ (M⁻¹ *ᵥ (C *ᵥ h)) := by
  simp only [connectorEnergy, optimizer, Matrix.mulVec_add, Matrix.mulVec_sub,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  ring

/-- Any linear endpoint injection gives a positive semidefinite eliminated
energy. In particular, this applies to the actual two-endpoint injection. -/
theorem eliminated_energy_nonneg {κ : Type*} [Fintype κ]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) (C : Matrix ι κ ℝ) (v : κ → ℝ) :
    0 ≤ (C *ᵥ v) ⬝ᵥ (M⁻¹ *ᵥ (C *ᵥ v)) := by
  simpa using hM.inv.posSemidef.dotProduct_mulVec_nonneg (C *ᵥ v)

theorem connectorEnergy_lower_bound {κ : Type*} [Fintype κ]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) (C : Matrix ι κ ℝ) (d : ℝ) (v : κ → ℝ) :
    d * (v ⬝ᵥ v) ≤ connectorEnergy M C d v := by
  have h := eliminated_energy_nonneg hM C v
  unfold connectorEnergy optimizer
  linarith

theorem connectorEnergy_curvature_lower_bound {κ : Type*} [Fintype κ]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) (C : Matrix ι κ ℝ)
    (d : ℝ) (v h : κ → ℝ) :
    (2 * d) * (h ⬝ᵥ h) ≤
      connectorEnergy M C d (v + h) + connectorEnergy M C d (v - h) -
        2 * connectorEnergy M C d v := by
  rw [connectorEnergy_second_difference]
  exact le_add_of_nonneg_right (eliminated_energy_nonneg hM C h)

/-- The actual connector Hessian is the strictly positive connector penalty
plus the positive semidefinite eliminated dual term. -/
theorem connector_hessian_posDef {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) (C : Matrix ι κ ℝ)
    {d : ℝ} (hd : 0 < d) :
    ((2 * d) • (1 : Matrix κ κ ℝ) + Cᵀ * M⁻¹ * C).PosDef := by
  have hquad : (Cᵀ * M⁻¹ * C).PosSemidef := by
    simpa using hM.inv.posSemidef.conjTranspose_mul_mul_same C
  exact (Matrix.PosDef.one.smul (show 0 < 2 * d by positivity)).add_posSemidef hquad

/-- The connector Hessian has the dimension-free quadratic lower bound `2d`. -/
theorem connector_hessian_lower_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) (C : Matrix ι κ ℝ)
    (d : ℝ) (v : κ → ℝ) :
    (2 * d) * (v ⬝ᵥ v) ≤
      v ⬝ᵥ (((2 * d) • (1 : Matrix κ κ ℝ) + Cᵀ * M⁻¹ * C) *ᵥ v) := by
  have hquad : (Cᵀ * M⁻¹ * C).PosSemidef := by
    simpa using hM.inv.posSemidef.conjTranspose_mul_mul_same C
  have hn : 0 ≤ v ⬝ᵥ ((Cᵀ * M⁻¹ * C) *ᵥ v) := by
    simpa using hquad.dotProduct_mulVec_nonneg v
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul]
  linarith

end PipeEnergy
end NCConcave16991

