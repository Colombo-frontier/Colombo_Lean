import VIReference.Pilot.RandomLower
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# A measurable Haar construction of a real Stiefel frame

This file constructs the genuinely random part of the prior used in
`RandomLower`: normalized Haar measure on the real orthogonal group and the
measurable map taking an orthogonal matrix to its first columns.  The remaining
analytic obligation is deliberately isolated at the end: mathlib still lacks
the conditional spherical projection estimate needed to fill
`SequentialFramePrior.adapted_slab_tail`.
-/

open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Matrix

namespace VIReference.Pilot

noncomputable section

/-- The orthogonal group in dimension `d`, with its induced Borel structure. -/
abbrev RealOrthogonalGroup (d : ℕ) := Matrix.orthogonalGroup (Fin d) ℝ

/-- Matrices do not carry a global measurable-space instance in mathlib,
because several matrix norms are available.  The canonical product topology is
unambiguous, so we explicitly choose its Borel sigma algebra here. -/
noncomputable instance realMatrixMeasurableSpace (d : ℕ) :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) := borel _

instance realMatrixBorelSpace (d : ℕ) :
    BorelSpace (Matrix (Fin d) (Fin d) ℝ) := ⟨rfl⟩

section CompactHaar

variable (d : ℕ)

theorem realOrthogonalGroup_isCompact :
    IsCompact (unitary (Matrix (Fin d) (Fin d) ℝ) :
      Set (Matrix (Fin d) (Fin d) ℝ)) := by
  apply isCompact_Icc.matrix.of_isClosed_subset isClosed_unitary
  intro Q hQ
  rw [Set.mem_matrix]
  intro i j
  have habs : |Q i j| ≤ 1 := by
    simpa [Real.norm_eq_abs] using entry_norm_bound_of_unitary hQ i j
  exact abs_le.mp habs

noncomputable instance realOrthogonalGroupCompactSpace : CompactSpace (RealOrthogonalGroup d) :=
  isCompact_iff_compactSpace.mp (realOrthogonalGroup_isCompact d)

/-- Normalized Haar probability on `O(d)`. -/
def orthogonalHaarCompact :
    TopologicalSpace.PositiveCompacts (RealOrthogonalGroup d) :=
  ⟨⟨Set.univ, CompactSpace.isCompact_univ⟩, by simpa using univ_nonempty⟩

/-- Normalized Haar probability on `O(d)`. -/
def orthogonalHaarProbability : Measure (RealOrthogonalGroup d) :=
  haarMeasure (orthogonalHaarCompact d)

instance orthogonalHaarProbability_isProbability :
    IsProbabilityMeasure (orthogonalHaarProbability d) where
  measure_univ := by
    simpa [orthogonalHaarProbability, orthogonalHaarCompact] using
      (haarMeasure_self (K₀ := orthogonalHaarCompact d))

instance orthogonalHaarProbability_isHaar :
    Measure.IsHaarMeasure (orthogonalHaarProbability d) := by
  change Measure.IsHaarMeasure (haarMeasure (orthogonalHaarCompact d))
  infer_instance

end CompactHaar

section Columns

variable {d : ℕ}

/-- Column `j` of an orthogonal matrix, as a vector in Euclidean space. -/
def orthogonalColumn (Q : RealOrthogonalGroup d) (j : Fin d) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => Q i j)

theorem measurable_orthogonalColumn (j : Fin d) :
    Measurable (fun Q : RealOrthogonalGroup d => orthogonalColumn Q j) := by
  apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
  refine measurable_pi_lambda _ fun i => ?_
  have hcoord : Continuous
      (fun Q : RealOrthogonalGroup d => (Q : Matrix (Fin d) (Fin d) ℝ) i j) := by
    have hm : Continuous
        (fun Q : Matrix (Fin d) (Fin d) ℝ => Q i j) :=
      (continuous_apply j).comp (continuous_apply i)
    exact hm.comp continuous_subtype_val
  exact hcoord.measurable

theorem orthonormal_orthogonalColumn (Q : RealOrthogonalGroup d) :
    Orthonormal ℝ (orthogonalColumn Q) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hQ : star (Q : Matrix (Fin d) (Fin d) ℝ) * Q = 1 := Q.property.1
  simpa [orthogonalColumn, Matrix.mul_apply, PiLp.inner_apply, Matrix.one_apply,
    mul_comm, eq_comm] using
    congrFun (congrFun hQ j) i

variable {N : ℕ} (hmd : hiddenM N ≤ d)

/-- The first `hiddenM N` columns of a Haar orthogonal matrix. -/
def haarStiefelFrame (Q : RealOrthogonalGroup d) :
    Fin (hiddenM N) → EuclideanSpace ℝ (Fin d) :=
  fun j => orthogonalColumn Q (Fin.castLE hmd j)

theorem measurable_haarStiefelFrame :
    Measurable (haarStiefelFrame hmd) := by
  refine measurable_pi_lambda _ fun j => ?_
  exact measurable_orthogonalColumn (Fin.castLE hmd j)

theorem orthonormal_haarStiefelFrame (Q : RealOrthogonalGroup d) :
    Orthonormal ℝ (haarStiefelFrame hmd Q) := by
  exact (orthonormal_orthogonalColumn Q).comp (Fin.castLE hmd) (Fin.castLE_injective hmd)

/-- The Stiefel law obtained by pushing normalized Haar probability on `O(d)`
to the first `hiddenM N` columns. -/
def haarStiefelLaw :
    Measure (Fin (hiddenM N) → EuclideanSpace ℝ (Fin d)) :=
  Measure.map (haarStiefelFrame hmd) (orthogonalHaarProbability d)

theorem haarStiefelLaw_isProbability :
    IsProbabilityMeasure (haarStiefelLaw hmd) := by
  exact Measure.isProbabilityMeasure_map (measurable_haarStiefelFrame hmd).aemeasurable

/-- Generator form of rotational invariance: multiplying the Haar matrix on
the left before taking its first columns does not change the Stiefel law. -/
theorem haarStiefel_generator_left_invariant (A : RealOrthogonalGroup d) :
    Measure.map (fun Q => haarStiefelFrame hmd (A * Q))
        (orthogonalHaarProbability d) =
      haarStiefelLaw hmd := by
  calc
    Measure.map (fun Q => haarStiefelFrame hmd (A * Q))
        (orthogonalHaarProbability d) =
        Measure.map (haarStiefelFrame hmd)
          (Measure.map (fun Q => A * Q) (orthogonalHaarProbability d)) := by
            symm
            rw [Measure.map_map (measurable_haarStiefelFrame hmd)
              (measurable_const_mul A)]
            rfl
    _ = Measure.map (haarStiefelFrame hmd) (orthogonalHaarProbability d) := by
      rw [map_mul_left_eq_self]
    _ = haarStiefelLaw hmd := rfl

end Columns

section SequentialInterface

variable {N d : ℕ} {R : ℝ} (hmd : hiddenM N ≤ d)

/-- In the theorem's probability regime, the displayed dimension condition
leaves at least one unused ambient direction. -/
theorem hiddenM_lt_of_randomDimensionCondition {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hdim : RandomDimensionCondition N d delta) : hiddenM N < d := by
  let m : ℝ := hiddenM N
  let A : ℝ := 2 * (m ^ 2 + 1) / delta
  have hm0 : 0 < m := by
    dsimp [m]
    exact_mod_cast hiddenM_pos N
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast hiddenM_pos N
  have hA1 : 1 < A := by
    dsimp [A]
    have hm_sq : 1 ≤ m ^ 2 := by nlinarith
    apply (lt_div_iff₀ hdelta0).2
    nlinarith
  have hpositive : 0 < 2048 * m ^ 3 * Real.log A := by
    exact mul_pos (mul_pos (by norm_num) (pow_pos hm0 3)) (Real.log_pos hA1)
  have hceil : 1 ≤ Nat.ceil (2048 * m ^ 3 * Real.log A) :=
    Nat.one_le_ceil_iff.mpr hpositive
  dsimp [RandomDimensionCondition] at hdim
  change d ≥ hiddenM N +
    Nat.ceil (2048 * m ^ 3 * Real.log A) at hdim
  omega

/-- The sole analytic bridge still needed to turn the concrete Haar/Stiefel
sample space into the `SequentialFramePrior` consumed by `RandomLower`.

This is a proposition, not an axiom.  It states the conditional-sphere slab
estimate for every prefix-adapted probe.  The sample space, probability,
measurability, and orthonormality are already concrete above. -/
def HaarStiefelAdaptedSlabTail : Prop :=
  ∀ (t : ℕ) (ht : t ≤ hiddenM N) (i : Fin (hiddenM N)) (hti : t ≤ i.1)
    (x : RealOrthogonalGroup d → EuclideanSpace ℝ (Fin d)),
    Measurable (fun Q => inner ℝ (haarStiefelFrame hmd Q i) (x Q)) →
    DependsOnlyOnFramePrefix (haarStiefelFrame hmd) t x →
    (∀ Q, ‖x Q‖ ≤ R) →
    MeasurableSet {Q | |inner ℝ (haarStiefelFrame hmd Q i) (x Q)| >
      hiddenTau R N / 2} →
    orthogonalHaarProbability d
      {Q | |inner ℝ (haarStiefelFrame hmd Q i) (x Q)| >
        hiddenTau R N / 2} ≤
      ENNReal.ofReal (randomSingleBadReal N d)

/-- A sharper, reusable statement of the missing conditional-sphere input.
Conditionally on a prefix, every later Haar column has the projection MGF of
a sphere of dimension at least `d-hiddenM N`.  Stating the weakest dimension
uniform in `i` makes the eventual union bound immediate. -/
def HaarStiefelAdaptedProjectionMGF (hR : 0 < R)
    (hmdlt : hiddenM N < d) : Prop :=
  ∀ (t : ℕ) (ht : t ≤ hiddenM N) (i : Fin (hiddenM N)) (hti : t ≤ i.1)
    (x : RealOrthogonalGroup d → EuclideanSpace ℝ (Fin d)),
    Measurable (fun Q => inner ℝ (haarStiefelFrame hmd Q i) (x Q)) →
    DependsOnlyOnFramePrefix (haarStiefelFrame hmd) t x →
    (∀ Q, ‖x Q‖ ≤ R) →
    HasSubgaussianMGF
      (fun Q => inner ℝ (haarStiefelFrame hmd Q i) (x Q))
      ⟨R ^ 2 / (d - hiddenM N : ℕ),
        div_nonneg (sq_nonneg R) (Nat.cast_nonneg _)⟩
      (orthogonalHaarProbability d)

/-- The conditional projection MGF is sufficient for the exact
`adapted_slab_tail` field, including the article's constant `2048`.
Thus the remaining geometric obligation is about conditional law/MGF only;
the Chernoff conversion and constant arithmetic are kernel checked here. -/
theorem haarStiefelAdaptedSlabTail_of_projectionMGF
    (hR : 0 < R) (hmdlt : hiddenM N < d)
    (hmgf : HaarStiefelAdaptedProjectionMGF (R := R) hmd hR hmdlt) :
    HaarStiefelAdaptedSlabTail (R := R) hmd := by
  intro t ht i hti x hmx hprefix hx hmeas
  let k : ℕ := d - hiddenM N
  have hk : 0 < k := Nat.sub_pos_of_lt hmdlt
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : 0 ≤ R ^ 2 / (k : ℝ) := div_nonneg (sq_nonneg R) hkR.le
  have ha : 0 < hiddenTau R N / 2 := div_pos (hiddenTau_pos hR N) (by norm_num)
  have htail := abs_tail_le_of_subgaussian_mgf
    (μ := orthogonalHaarProbability d) hc ha
    (hmgf t ht i hti x hmx hprefix hx)
  have hrewrite :
      2 * Real.exp (-(hiddenTau R N / 2) ^ 2 /
          (2 * (R ^ 2 / (k : ℝ)))) = randomSingleBadReal N d := by
    have halgebra :
        (hiddenTau R N / 2) ^ 2 / (2 * (R ^ 2 / (k : ℝ))) =
          (k : ℝ) * (hiddenTau R N / 2) ^ 2 / (2 * R ^ 2) := by
      field_simp [hR.ne', hkR.ne']
    have halgebraNeg :
        -(hiddenTau R N / 2) ^ 2 / (2 * (R ^ 2 / (k : ℝ))) =
          -((k : ℝ) * (hiddenTau R N / 2) ^ 2 / (2 * R ^ 2)) := by
      rw [neg_div, halgebra]
    rw [halgebraNeg, hiddenTau_slab_exponent N k hR]
    simp [randomSingleBadReal, k]
    <;> ring
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (htail.trans_eq hrewrite)

/-- Package the concrete Haar sample space as a `SequentialFramePrior` once
the isolated adapted-tail bridge has been supplied. -/
def haarSequentialFramePrior
    (htail : HaarStiefelAdaptedSlabTail (R := R) hmd) :
    SequentialFramePrior (EuclideanSpace ℝ (Fin d)) N d R where
  Omega := RealOrthogonalGroup d
  measurableSpace := inferInstance
  measure := orthogonalHaarProbability d
  probability := orthogonalHaarProbability_isProbability d
  frame := haarStiefelFrame hmd
  orthonormal := orthonormal_haarStiefelFrame hmd
  adapted_slab_tail := htail

/-- Fully concrete prior constructor from the single conditional-MGF bridge. -/
def haarSequentialFramePriorOfProjectionMGF
    (hR : 0 < R) (hmdlt : hiddenM N < d)
    (hmgf : HaarStiefelAdaptedProjectionMGF (R := R) hmd hR hmdlt) :
    SequentialFramePrior (EuclideanSpace ℝ (Fin d)) N d R :=
  haarSequentialFramePrior hmd
    (haarStiefelAdaptedSlabTail_of_projectionMGF hmd hR hmdlt hmgf)

@[simp] theorem haarSequentialFramePrior_frame
    (htail : HaarStiefelAdaptedSlabTail (R := R) hmd)
    (Q : RealOrthogonalGroup d) :
    (haarSequentialFramePrior hmd htail).frame Q = haarStiefelFrame hmd Q := rfl

theorem measurable_haarSequentialFramePrior_frame
    (htail : HaarStiefelAdaptedSlabTail (R := R) hmd) :
    Measurable (haarSequentialFramePrior hmd htail).frame := by
  exact measurable_haarStiefelFrame hmd

end SequentialInterface

end


end VIReference.Pilot
