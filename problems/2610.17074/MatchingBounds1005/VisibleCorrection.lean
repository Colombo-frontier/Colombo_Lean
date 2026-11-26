import MatchingBounds1005.OracleReconstruction
import MatchingBounds1005.VisibleReadouts

/-! Zero-filled hidden readout entries yield exactly the disclosed correction
function, hence exactly its value and gradient at every point. -/
noncomputable section
open scoped BigOperators InnerProductSpace

namespace MatchingBounds1005.TensorGeometry

theorem correctionSum_zeroFilled {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (b : ι → Vec d) (τ A : ℝ) {r : ℝ} (hr : 1 ≤ r) (S : Finset ι) :
    correctionSum (fun i => if i ∈ S then b i else 0) τ r A Finset.univ =
      correctionSum b τ r A S := by
  have hc : Primitive.correction r 0 = 0 := Primitive.correction_core hr (by simpa only [abs_zero] using (show (0 : ℝ) ≤ r by linarith))
  funext x
  unfold correctionSum
  congr 1
  calc
    _ = ∑ i ∈ S, Primitive.correction r (A * ⟪if i ∈ S then b i else 0, x⟫_ℝ) :=
      (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp only [if_neg hi,
        inner_zero_left, mul_zero, hc])).symm
    _ = _ := Finset.sum_congr rfl (fun i hi => by rw [if_pos hi])

theorem correctionSum_visibleAt {d N : ℕ} (b : Fin N → Vec d)
    (U : Vec d →L[ℝ] Vec d) (disclose : Fin N → ℕ) (t : ℕ)
    (τ A : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    correctionSum (VisibleReadouts.visibleAt disclose b U t) τ r A Finset.univ =
      correctionSum (fun i => U (b i)) τ r A (Finset.univ.filter (fun i => disclose i ≤ t)) := by
  have heq : VisibleReadouts.visibleAt disclose b U t =
      fun i => if i ∈ Finset.univ.filter (fun i => disclose i ≤ t) then U (b i) else 0 := by
    funext i
    simp only [VisibleReadouts.visibleAt, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq]
  exact correctionSum_zeroFilled _ _ _ hr _

theorem correctionOracle_visibleAt {d N : ℕ} (b : Fin N → Vec d)
    (U : Vec d →L[ℝ] Vec d) (disclose : Fin N → ℕ) (t : ℕ)
    (τ A : ℝ) {r : ℝ} (hr : 1 ≤ r) (x : Vec d) :
    Model.oracle (correctionSum (VisibleReadouts.visibleAt disclose b U t) τ r A Finset.univ) x =
      Model.oracle (correctionSum (fun i => U (b i)) τ r A
        (Finset.univ.filter (fun i => disclose i ≤ t))) x := by
  rw [correctionSum_visibleAt b U disclose t τ A hr]

end MatchingBounds1005.TensorGeometry
