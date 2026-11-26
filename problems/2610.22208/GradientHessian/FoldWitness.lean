import GradientHessian.Fold

/-!
The eight-coordinate stationary witness for the actual two-level localized
expression in the folding appendix. The full hierarchy must still be shown to
equal this expression near the witness; that identification is not assumed here.
-/

noncomputable section

namespace GradientHessian.Localized

open Filter
open scoped Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

/-- A folded coordinate after the child has completed and the parent ports are zero. -/
def foldedCoordinate (R w : ℝ) (a b : E) (first : Bool) (u : E) : ℝ :=
  potential R w a u + if first then
    potential (6 * R) (3 * w) b u - incoming (6 * R) (3 * w) b u
  else potential (6 * R) (3 * w) b u

omit [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E] in
private theorem foldedCoordinate_eventually {R w : ℝ} (hw : 0 < w)
    (a b u : E) (first : Bool) (hlo : ‖u - a‖ < w) (hhi : 9 * w < ‖u - b‖) :
    foldedCoordinate R w a b first =ᶠ[𝓝 u]
      (fun v => well R w a v +
        (if first then drive (3 * w) b v - 512 * (6 * R) else publicPotential (6 * R) v)) := by
  have hca : ContinuousAt (fun v : E => ‖v - a‖) u :=
    (continuous_id.sub continuous_const).norm.continuousAt
  have hcb : ContinuousAt (fun v : E => ‖v - b‖) u :=
    (continuous_id.sub continuous_const).norm.continuousAt
  have ha : ∀ᶠ v in 𝓝 u, ‖v - a‖ < 2 * w :=
    hca.preimage_mem_nhds (gt_mem_nhds (by linarith : ‖u - a‖ < 2 * w))
  have hb : ∀ᶠ v in 𝓝 u, 9 * w < ‖v - b‖ := hcb.preimage_mem_nhds (lt_mem_nhds hhi)
  filter_upwards [ha, hb] with v hva hvb
  unfold foldedCoordinate
  rw [potential_eq_well_of_norm_le_two_mul hw hva.le]
  cases first
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [potential, perturbation_eq_zero_of_three_mul_le_norm (by positivity)
      (by linarith : 3 * (3 * w) ≤ ‖v - b‖), add_zero]
  · simp only [↓reduceIte, cancellation]

/-- Every pair of centers at radii R and 6R admits the stationary folded coordinate. -/
theorem exists_folded_coordinate {R w : ℝ} (hw : 0 < w) (hscale : 16 * w ≤ R)
    (a b : E) (ha : ‖a‖ = R) (hb : ‖b‖ = 6 * R) (first : Bool) :
    ∃ u : E, HasFDerivAt (𝕜 := ℝ) (foldedCoordinate R w a b first) 0 u ∧
      ‖u - a‖ < w ∧ port w a u = 1 ∧ port (3 * w) b u = 0 := by
  have hR : 0 < R := by linarith
  cases first
  · obtain ⟨u, _, hder, hdist⟩ := exists_well_public_minimizer hw
      (by positivity : 0 < 6 * R) R a
    have hsep := adjacent_level_separation hw hscale ha hb hdist
    have heq := foldedCoordinate_eventually (R := R) hw a b u false hdist hsep
    have hf : HasFDerivAt (𝕜 := ℝ) (foldedCoordinate R w a b false) 0 u := by
      have hd : HasFDerivAt (𝕜 := ℝ) (fun v => well R w a v + publicPotential (6 * R) v) 0 u :=
        by simpa only [map_zero] using hder.hasFDerivAt
      apply hd.congr_of_eventuallyEq
      simpa only [Bool.false_eq_true, ↓reduceIte] using heq
    exact ⟨u, hf, hdist, port_eq_one_of_norm_le hw hdist.le,
      (adjacent_parent_port_zero hw hscale ha hb hdist).1⟩
  · obtain ⟨u, _, hder, hdist⟩ := exists_well_drive_minimizer hw
      (by positivity : 0 < 3 * w) R a b
    have hsep := adjacent_level_separation hw hscale ha hb hdist
    have heq := foldedCoordinate_eventually (R := R) hw a b u true hdist hsep
    have hfbase : HasFDerivAt (𝕜 := ℝ)
        (fun v => well R w a v + (drive (3 * w) b v - 512 * (6 * R))) 0 u := by
      have h := hder.hasFDerivAt.sub_const (512 * (6 * R))
      simpa only [map_zero, sub_eq_add_neg, add_assoc] using h
    have hf := hfbase.congr_of_eventuallyEq (by simpa only [↓reduceIte] using heq)
    exact ⟨u, hf, hdist, port_eq_one_of_norm_le hw hdist.le,
      (adjacent_parent_port_zero hw hscale ha hb hdist).1⟩

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The literal local folded sum, with a generic stationary lower baseline. -/
def foldedLocal (Q : Y → ℝ) (C R w : ℝ) (a b : Fin 8 → E)
    (z : Y × (Fin 8 → E)) : ℝ :=
  Q z.1 + C + ∑ i, foldedCoordinate R w (a i) (b i) (decide (i = 0)) (z.2 i)

/-- The actual eight-coordinate folded expression has a stationary point with
all parent ports zero and all child ports one. This result does not assert the
separate hierarchy-to-local-expression identity. -/
theorem exists_folded_local_stationary {R w : ℝ} (hw : 0 < w) (hscale : 16 * w ≤ R)
    (a b : Fin 8 → E) (ha : ∀ i, ‖a i‖ = R) (hb : ∀ i, ‖b i‖ = 6 * R)
    (Q : Y → ℝ) (hQ : HasFDerivAt (𝕜 := ℝ) Q 0 0) (C : ℝ) :
    ∃ U : Fin 8 → E, HasFDerivAt (𝕜 := ℝ) (foldedLocal Q C R w a b) 0 (0, U) ∧
      (∀ i, ‖U i - a i‖ < w) ∧ (∀ i, port w (a i) (U i) = 1) ∧
      (∀ i, port (3 * w) (b i) (U i) = 0) := by
  classical
  have hex := fun i : Fin 8 => exists_folded_coordinate hw hscale (a i) (b i)
    (ha i) (hb i) (decide (i = 0))
  choose U hU hdist hchild hparent using hex
  have hterms : ∀ i : Fin 8, HasFDerivAt (𝕜 := ℝ)
      (fun z : Y × (Fin 8 → E) => foldedCoordinate R w (a i) (b i) (decide (i = 0)) (z.2 i))
      0 (0, U) := by
    intro i
    have hi := (hasFDerivAt_apply (𝕜 := ℝ) i U).comp ((0 : Y), U)
      (hasFDerivAt_snd (𝕜 := ℝ) (E := Y) (F := Fin 8 → E))
    simpa only [ContinuousLinearMap.zero_comp] using (hU i).comp ((0 : Y), U) hi
  have hsum : HasFDerivAt (𝕜 := ℝ)
      (fun z : Y × (Fin 8 → E) => ∑ i, foldedCoordinate R w (a i) (b i)
        (decide (i = 0)) (z.2 i)) 0 (0, U) := by
    simpa using HasFDerivAt.sum (u := Finset.univ) (fun i _ => hterms i)
  have hbase : HasFDerivAt (𝕜 := ℝ) (fun z : Y × (Fin 8 → E) => Q z.1 + C) 0 (0, U) := by
    simpa using (hQ.comp ((0 : Y), U)
      (hasFDerivAt_fst (𝕜 := ℝ) (E := Y) (F := Fin 8 → E))).add_const C
  refine ⟨U, ?_, hdist, hchild, hparent⟩
  simpa only [foldedLocal, add_zero] using hbase.add hsum

end GradientHessian.Localized
