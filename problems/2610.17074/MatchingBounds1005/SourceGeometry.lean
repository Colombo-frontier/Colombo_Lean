import MatchingBounds1005.ChainCalendar
import MatchingBounds1005.ChainSpectral

/-! # The source calendar and source spectral geometry in common coordinates -/
noncomputable section
open scoped InnerProductSpace
open MatchingBounds1005.GaussianVector

namespace MatchingBounds1005.PathLayers
open BlockGeometry PathGreen

theorem source_base_dimension (M n : ℕ) :
    baseDimension (E := EuclideanSpace ℝ (Fin (M + 1))) n = (n + 1) * (M + 1) := by
  change Module.finrank ℝ (PiLp 2 (fun _ : Fin (n + 1) => EuclideanSpace ℝ (Fin (M + 1)))) = _
  rw [(WithLp.linearEquiv 2 ℝ (Fin (n + 1) → EuclideanSpace ℝ (Fin (M + 1)))).finrank_eq]
  simp [Module.finrank_pi_fintype]

theorem source_copy_dimension (M n K : ℕ) :
    copyDimension (E := EuclideanSpace ℝ (Fin (M + 1))) n K =
      (K + 1) * ((n + 1) * (M + 1)) := by
  rw [copyDimension_eq, source_base_dimension]

def ambientLayerSpace (M n K jstar t : ℕ) : Submodule ℝ
    (Vec (copyDimension (E := EuclideanSpace ℝ (Fin (M + 1))) n K)) :=
  (copyLayerSpace M n K jstar t).map (copyEuclideanIso n K).symm.toLinearEquiv.toLinearMap

theorem ambientLayerSpace_mono (M n K jstar : ℕ) : Monotone (ambientLayerSpace M n K jstar) := by
  intro t u htu
  exact Submodule.map_mono ((copyLayerSpace_mono M n K jstar) htu)

theorem ambientLayerSpace_le_active (M n K jstar t : ℕ) :
    ambientLayerSpace M n K jstar t ≤
      copyAmbientActiveSpace (E := EuclideanSpace ℝ (Fin (M + 1))) n K :=
  Submodule.map_mono (copyLayerSpace_le_active M n K jstar t)

theorem actual_ambient_layer_propagation (L h A : ℝ) (hL : 0 < L) (hh : 0 < h)
    (hhsmall : h ≤ 1 / 4) (hA : 0 < A) (n K t : ℕ) :
    (ambientLayerSpace (pathEdges h) n K ((pathEdges h + 2) / 2) t).map
      ((actualBlockGeometry L h A hL hh hhsmall hA).copyAmbientOperator n K).toLinearMap ≤
        ambientLayerSpace (pathEdges h) n K ((pathEdges h + 2) / 2) (t + 1) := by
  rintro x ⟨z, ⟨v, hv, rfl⟩, rfl⟩
  refine ⟨(actualBlockGeometry L h A hL hh hhsmall hA).copyOperator n K v, ?_, ?_⟩
  · exact actual_copy_layer_propagation L h A hL hh hhsmall hA n K t ⟨v, hv, rfl⟩
  · simp [copyAmbientOperator]

def ambientReadout (A : ℝ) (M n K : ℕ) (s : Fin (n + 1)) :
    Vec (copyDimension (E := EuclideanSpace ℝ (Fin (M + 1))) n K) :=
  (copyEuclideanIso n K).symm (activeInsert n K (blockVector M n s (suffixVector A M)))

theorem ambientReadout_mem_active (A : ℝ) (M n K : ℕ) (s : Fin (n + 1)) :
    ambientReadout A M n K s ∈
      copyAmbientActiveSpace (E := EuclideanSpace ℝ (Fin (M + 1))) n K :=
  ⟨_, ⟨_, rfl⟩, rfl⟩

theorem ambientReadout_hidden (A : ℝ) (M n K t : ℕ) (s : Fin (n + 1))
    (ht : t < (s.val + 1) * ((M + 2) / 2)) :
    ambientReadout A M n K s ∈ (ambientLayerSpace M n K ((M + 2) / 2) t)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro x ⟨z, hz, rfl⟩
  change ⟪(copyEuclideanIso n K).symm z, (copyEuclideanIso n K).symm
    (activeInsert n K (blockVector M n s (suffixVector A M)))⟫_ℝ = 0
  rw [(copyEuclideanIso (E := EuclideanSpace ℝ (Fin (M + 1))) n K).symm.inner_map_map]
  exact (Submodule.mem_orthogonal _ _).mp (copy_readout_hidden A M n K t s ht) z hz

theorem ambientReadout_disclosed (A : ℝ) (M n K t : ℕ) (s : Fin (n + 1))
    (ht : (s.val + 1) * ((M + 2) / 2) ≤ t) :
    ambientReadout A M n K s ∈ ambientLayerSpace M n K ((M + 2) / 2) t :=
  ⟨_, copy_readout_disclosed A M n K t s ht, rfl⟩

end MatchingBounds1005.PathLayers
