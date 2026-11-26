import GradientHessian.FoldWitness
import GradientHessian.Hierarchy

/-! The adjacent-level diagonal restriction instantiated with literal hierarchy
nodes. Descendant and sibling functions are arbitrary: exact plateau identities
eliminate them on a neighborhood of the constructed stationary point. -/

noncomputable section

namespace GradientHessian.FoldHierarchy

open Localized Filter
open scoped BigOperators Topology

variable {E Y Z : Type*}

def eight (f : Fin 8 → Z → ℝ) (i : ℕ) (z : Z) : ℝ :=
  if hi : i < 8 then f ⟨i, hi⟩ z else 0

theorem eight_fin (f : Fin 8 → Z → ℝ) (i : Fin 8) (z : Z) : eight f i z = f i z := by
  simp [eight, i.isLt]

theorem sum_eight (f : Fin 8 → Z → ℝ) (z : Z) :
    (∑ i ∈ Finset.range 8, eight f i z) = ∑ i, f i z := by
  simpa only [eight_fin] using (Fin.sum_univ_eq_sum_range (fun i => eight f i z) 8).symm

variable [NormedAddCommGroup E] [NormedAddCommGroup Y]

def lowerSelf (R w : ℝ) (a : Fin 8 → E) : ℕ → (Y × (Fin 8 → E)) → ℝ :=
  eight (fun i z => potential R w (a i) (z.2 i))
def lowerIncoming (R w : ℝ) (a : Fin 8 → E) : ℕ → (Y × (Fin 8 → E)) → ℝ :=
  eight (fun i z => incoming R w (a i) (z.2 i))
def lowerPort (w : ℝ) (a : Fin 8 → E) : ℕ → (Y × (Fin 8 → E)) → ℝ :=
  eight (fun i z => port w (a i) (z.2 i))

def completedChild (Q : Y → ℝ) (S R w : ℝ) (a : Fin 8 → E)
    (desc descPort : ℕ → (Y × (Fin 8 → E)) → ℝ) : (Y × (Fin 8 → E)) → ℝ :=
  Hierarchy.nodeScalar 8 (fun z => Q z.1) S desc descPort
    (lowerSelf R w a) (lowerIncoming R w a) (lowerPort w a)

/-- Literal parent and first-child node formulas, after identifying their eight
register arrays. The parent baseline is the manuscript's common public baseline. -/
def diagonalNode (Q : Y → ℝ) (S₀ S₁ R w : ℝ) (a b : Fin 8 → E)
    (desc descPort siblings siblingPort : ℕ → (Y × (Fin 8 → E)) → ℝ) :
    (Y × (Fin 8 → E)) → ℝ :=
  Hierarchy.nodeScalar 8 (fun z => Q z.1 + ∑ i, publicPotential R (z.2 i)) S₁
    (fun i z => if i = 0 then completedChild Q S₀ R w a desc descPort z else siblings i z)
    (fun i z => if i = 0 then port w (a 7) (z.2 7) else siblingPort i z)
    (lowerSelf (6 * R) (3 * w) b) (lowerIncoming (6 * R) (3 * w) b)
    (lowerPort (3 * w) b)

theorem sum_foldedCoordinate (R w : ℝ) (a b U : Fin 8 → E) :
    (∑ i, foldedCoordinate R w (a i) (b i) (decide (i = 0)) (U i)) =
      (∑ i, potential R w (a i) (U i)) +
      (∑ i, potential (6 * R) (3 * w) (b i) (U i)) -
      incoming (6 * R) (3 * w) (b 0) (U 0) := by
  have heq : ∀ i : Fin 8,
      foldedCoordinate R w (a i) (b i) (decide (i = 0)) (U i) =
      potential R w (a i) (U i) + potential (6 * R) (3 * w) (b i) (U i) -
        (if i = 0 then incoming (6 * R) (3 * w) (b i) (U i) else 0) := by
    intro i
    by_cases hi : i = 0
    · simp [foldedCoordinate, hi]
      ring
    · simp [foldedCoordinate, hi]
  simp_rw [heq]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]

omit [NormedAddCommGroup Y] in
theorem diagonalNode_eq_local (Q : Y → ℝ) (S₀ S₁ R w : ℝ) (a b : Fin 8 → E)
    (desc descPort siblings siblingPort : ℕ → (Y × (Fin 8 → E)) → ℝ)
    (z : Y × (Fin 8 → E))
    (hlo : ∀ i : Fin 8, port w (a i) (z.2 i) = 1)
    (hhi : port (3 * w) (b 0) (z.2 0) = 0) :
    diagonalNode Q S₀ S₁ R w a b desc descPort siblings siblingPort z =
      foldedLocal Q (-8 * S₀) R w a b z := by
  unfold diagonalNode
  rw [Hierarchy.node_first_unfinished _ _ _ _ _ _ _ _ _ (k := 0)
    (by norm_num) (by omega) (by simpa [lowerPort, eight] using hhi)]
  simp only [↓reduceIte, Nat.cast_zero, zero_mul, sub_zero, hlo 7, mul_one]
  unfold completedChild
  rw [Hierarchy.node_completed _ _ _ _ _ _ _ _ _ (by
    intro i hi
    simpa [lowerPort, eight, hi] using hlo ⟨i, hi⟩)]
  simp only [lowerSelf, lowerIncoming, eight_fin, sum_eight]
  simp only [foldedLocal, sum_foldedCoordinate]
  norm_num [eight]
  ring

variable [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E] [NormedSpace ℝ Y]

/-- The actual two-level hierarchy diagonal restriction has an uncertified stationary point,
for every choice of descendants and siblings. No claims about derivatives of those arbitrary
functions are needed, because their coefficients vanish on a neighborhood. -/
theorem diagonalNode_has_uncertified_stationary {R w : ℝ} (hw : 0 < w)
    (hscale : 16 * w ≤ R) (a b : Fin 8 → E)
    (ha : ∀ i, ‖a i‖ = R) (hb : ∀ i, ‖b i‖ = 6 * R)
    (Q : Y → ℝ) (hQ : HasFDerivAt (𝕜 := ℝ) Q 0 0) (S₀ S₁ : ℝ)
    (desc descPort siblings siblingPort : ℕ → (Y × (Fin 8 → E)) → ℝ) :
    ∃ U : Fin 8 → E,
      HasFDerivAt (𝕜 := ℝ) (diagonalNode Q S₀ S₁ R w a b desc descPort siblings siblingPort)
        0 (0, U) ∧ (∀ i, port (3 * w) (b i) (U i) = 0) := by
  obtain ⟨U, hder, hdist, _, hparent⟩ :=
    exists_folded_local_stationary hw hscale a b ha hb Q hQ (-8 * S₀)
  have hlo : ∀ᶠ z : Y × (Fin 8 → E) in 𝓝 ((0 : Y), U),
      ∀ i : Fin 8, port w (a i) (z.2 i) = 1 := by
    apply Filter.eventually_all.2
    intro i
    have hc : ContinuousAt (fun z : Y × (Fin 8 → E) => ‖z.2 i - a i‖) (0, U) := by
      fun_prop
    filter_upwards [hc.preimage_mem_nhds (gt_mem_nhds (hdist i))] with z hz
    exact port_eq_one_of_norm_le hw (le_of_lt hz)
  have hsep := adjacent_level_separation hw hscale (ha 0) (hb 0) (hdist 0)
  have hhi : ∀ᶠ z : Y × (Fin 8 → E) in 𝓝 ((0 : Y), U),
      port (3 * w) (b 0) (z.2 0) = 0 := by
    have hc : ContinuousAt (fun z : Y × (Fin 8 → E) => ‖z.2 0 - b 0‖) (0, U) := by
      fun_prop
    filter_upwards [hc.preimage_mem_nhds (lt_mem_nhds hsep)] with z hz
    change 9 * w < ‖z.2 0 - b 0‖ at hz
    exact port_eq_zero_of_two_mul_le_norm (by positivity) (by linarith)
  refine ⟨U, hder.congr_of_eventuallyEq ?_, hparent⟩
  filter_upwards [hlo, hhi] with z hzl hzh
  exact diagonalNode_eq_local Q S₀ S₁ R w a b desc descPort siblings siblingPort z hzl hzh

end GradientHessian.FoldHierarchy
