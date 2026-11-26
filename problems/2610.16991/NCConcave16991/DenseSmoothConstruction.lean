import NCConcave16991.DenseSmoothGate
import NCConcave16991.DenseSmoothChainAverage
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Literal fixed-table finite-sum radial chains from Appendix C -/

noncomputable section

namespace NCConcave16991.DenseSmooth

open Set
open scoped InnerProductSpace BigOperators ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Blocks (E : Type*) (T : ℕ) := PiLp 2 (fun _ : Fin (T + 1) ↦ E)

def blockProjection {T : ℕ} (j : Fin (T + 1)) : Blocks E T →L[ℝ] E :=
  PiLp.proj 2 (fun _ : Fin (T + 1) ↦ E) j

/-- Structural data of an actual fixed table. These fields specify unit rows
and the literal table average; no analytic or lower-bound conclusion is a field. -/
structure Table (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n T : ℕ) (ρ : ℝ) where
  direction : Fin (T + 1) → E
  row : Fin n → Fin (T + 1) → E
  direction_unit : ∀ j, ‖direction j‖ = 1
  row_unit : ∀ i j, ‖row i j‖ = 1
  row_sum : ∀ j, ∑ i, row i j = ((n : ℝ) * ρ) • direction j

def coordinate {T : ℕ} (u : Fin (T + 1) → E) (x : Blocks E T) (j : Fin (T + 1)) : ℝ :=
  radialCoordinate (u j) (x j)

def componentChain {n T : ℕ} (ρ : ℝ) (u : Fin (T + 1) → E)
    (rows : Fin n → Fin (T + 1) → E) (i : Fin n) (x : Blocks E T) : ℝ :=
  -scaledRadialCoordinate ρ (rows i 0) (x 0) -
    ∑ j : Fin T, gate (coordinate u x j.castSucc) *
      (scaledRadialCoordinate ρ (rows i j.succ) (x j.succ) + 1) +
    (33 / 32 : ℝ) * ‖x‖ ^ 2

def meanChain {T : ℕ} (u : Fin (T + 1) → E) (x : Blocks E T) : ℝ :=
  -coordinate u x 0 - ∑ j : Fin T,
    gate (coordinate u x j.castSucc) * (coordinate u x j.succ + 1) +
    (33 / 32 : ℝ) * ‖x‖ ^ 2

theorem componentChain_average {n T : ℕ} [NeZero n] {ρ : ℝ} (hρ : ρ ≠ 0)
    (u : Fin (T + 1) → E) (rows : Fin n → Fin (T + 1) → E)
    (hrows : ∀ j, ∑ i, rows i j = ((n : ℝ) * ρ) • u j) (x : Blocks E T) :
    (∑ i, componentChain ρ u rows i x) / n = meanChain u x := by
  exact average_abstractComponentRadialChain
    (fun i j ↦ scaledRadialCoordinate ρ (rows i j) (x j))
    (coordinate u x) (fun j ↦ gate (coordinate u x j.castSucc)) ((33 / 32 : ℝ) * ‖x‖ ^ 2)
    (fun j ↦ average_scaledRadialCoordinate hρ (fun i ↦ rows i j) (u j) (x j) (hrows j))

theorem meanChain_lower {T : ℕ} (u : Fin (T + 1) → E)
    (hu : ∀ j, ‖u j‖ = 1) (x : Blocks E T) :
    -2 * (T + 1 : ℕ) ≤ meanChain u x := by
  have hh := abstractRadialChain_lower (coordinate u x)
    (fun j ↦ gate (coordinate u x j.castSucc)) ((33 / 32 : ℝ) * ‖x‖ ^ 2)
    (fun j ↦ (abs_radialCoordinate_lt_one (hu j) (x j)).le)
    (fun j ↦ gate_mem_Icc _) (by positivity)
  change -1 - 2 * (T : ℝ) ≤ meanChain u x at hh
  push_cast
  linarith

@[simp] theorem coordinate_zero {T : ℕ} (u : Fin (T + 1) → E) (j : Fin (T + 1)) :
    coordinate u (0 : Blocks E T) j = 0 := by simp [coordinate, radialCoordinate]

@[simp] theorem meanChain_zero {T : ℕ} (u : Fin (T + 1) → E) : meanChain u 0 = 0 := by
  simp [meanChain, gate_zero (by norm_num : (0 : ℝ) ≤ 5 / 32)]

theorem meanChain_boundedBelow {T : ℕ} (u : Fin (T + 1) → E) (hu : ∀ j, ‖u j‖ = 1) :
    BddBelow (range (meanChain u)) := by
  exact ⟨-2 * (T + 1 : ℕ), by rintro y ⟨x, rfl⟩; exact meanChain_lower u hu x⟩

theorem meanChain_initialGap {T : ℕ} (u : Fin (T + 1) → E) (hu : ∀ j, ‖u j‖ = 1) :
    meanChain u 0 - sInf (range (meanChain u)) ≤ 2 * (T + 1 : ℕ) := by
  have hnonempty : (range (meanChain u)).Nonempty := range_nonempty _
  have hh := le_csInf hnonempty (show ∀ y ∈ range (meanChain u), -2 * (T + 1 : ℕ) ≤ y by
    rintro y ⟨x, rfl⟩; exact meanChain_lower u hu x)
  rw [meanChain_zero]
  linarith

theorem coordinate_contDiff {T : ℕ} (u : Fin (T + 1) → E) (j : Fin (T + 1)) :
    ContDiff ℝ ∞ (fun x : Blocks E T ↦ coordinate u x j) := by
  exact (radialCoordinate_contDiff (u j)).comp (blockProjection (E := E) j).contDiff

theorem componentChain_contDiff {n T : ℕ} (ρ : ℝ) (u : Fin (T + 1) → E)
    (rows : Fin n → Fin (T + 1) → E) (i : Fin n) :
    ContDiff ℝ ∞ (componentChain ρ u rows i) := by
  have hr (j : Fin (T + 1)) : ContDiff ℝ ∞
      (fun x : Blocks E T ↦ scaledRadialCoordinate ρ (rows i j) (x j)) :=
    contDiff_const.mul ((radialCoordinate_contDiff (rows i j)).comp
      (blockProjection (E := E) j).contDiff)
  exact (((hr 0).neg).sub (ContDiff.sum (fun j _ ↦
    (gate_contDiff.comp (coordinate_contDiff u j.castSucc)).mul ((hr j.succ).add contDiff_const)))).add
      (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem meanChain_contDiff {T : ℕ} (u : Fin (T + 1) → E) : ContDiff ℝ ∞ (meanChain u) := by
  exact (((coordinate_contDiff u 0).neg).sub (ContDiff.sum (fun j _ ↦
    (gate_contDiff.comp (coordinate_contDiff u j.castSucc)).mul
      ((coordinate_contDiff u j.succ).add contDiff_const)))).add
        (contDiff_const.mul (contDiff_norm_sq ℝ))

end NCConcave16991.DenseSmooth
