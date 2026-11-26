import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic

/-! Real matrix positivity and trace inequalities used in the manuscript.
No probabilistic assumptions enter this module. -/

namespace LowRank

open Matrix
open scoped Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- Loewner order, distinguished from the entrywise order on matrices. -/
def LoewnerLE (A B : Matrix n n ℝ) : Prop := (B - A).PosSemidef

theorem psd_diagonal_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef) (i : n) :
    0 ≤ A i i := by
  simpa using hA.2 (Pi.single i 1)

theorem psd_trace_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    0 ≤ A.trace :=
  Finset.sum_nonneg (fun i _ => psd_diagonal_nonneg hA i)

theorem psd_trace_mul_nonneg {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hp := psd_trace_nonneg (hB.conjTranspose_mul_mul_same hA.sqrt)
  rw [hA.posSemidef_sqrt.isHermitian.eq, Matrix.trace_mul_cycle,
    hA.sqrt_mul_self] at hp
  exact hp

theorem trace_mul_mono {P A B : Matrix n n ℝ}
    (hP : P.PosSemidef) (hAB : LoewnerLE A B) :
    (P * A).trace ≤ (P * B).trace := by
  have h := psd_trace_mul_nonneg hP hAB
  rw [mul_sub, Matrix.trace_sub] at h
  linarith

/-- The usual algebraic characterization of an orthogonal projector. -/
structure IsOrthogonalProjector (P : Matrix n n ℝ) : Prop where
  symmetric : Pᵀ = P
  idempotent : P * P = P

theorem IsOrthogonalProjector.posSemidef {P : Matrix n n ℝ}
    (hP : IsOrthogonalProjector P) : P.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  simpa only [conjTranspose_eq_transpose_of_trivial, hP.symmetric, hP.idempotent] using h

theorem IsOrthogonalProjector.complement {P : Matrix n n ℝ}
    (hP : IsOrthogonalProjector P) : IsOrthogonalProjector (1 - P) := by
  constructor
  · simp [transpose_sub, hP.symmetric]
  · noncomm_ring [hP.idempotent]

theorem IsOrthogonalProjector.le_one {P : Matrix n n ℝ}
    (hP : IsOrthogonalProjector P) : LoewnerLE P 1 := hP.complement.posSemidef

theorem projector_trace_mul_le_trace {P A : Matrix n n ℝ}
    (hP : IsOrthogonalProjector P) (hA : A.PosSemidef) :
    (P * A).trace ≤ A.trace := by
  have h := psd_trace_mul_nonneg hP.complement.posSemidef hA
  rw [sub_mul, one_mul, Matrix.trace_sub] at h
  linarith

theorem projector_overlap_nonneg {P K : Matrix n n ℝ}
    (hP : IsOrthogonalProjector P) (hK : IsOrthogonalProjector K) :
    0 ≤ (P * K).trace := psd_trace_mul_nonneg hP.posSemidef hK.posSemidef

theorem projector_overlap_le {P K : Matrix n n ℝ}
    (hP : IsOrthogonalProjector P) (hK : IsOrthogonalProjector K) :
    (P * K).trace ≤ P.trace := by
  rw [Matrix.trace_mul_comm]
  exact projector_trace_mul_le_trace hK hP.posSemidef

theorem psd_smul {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) : (c • A).PosSemidef := by
  constructor
  · change (c • A)ᴴ = c • A
    rw [conjTranspose_smul, star_trivial, hA.isHermitian.eq]
  · intro x
    simpa only [smul_mulVec_assoc, dotProduct_smul, smul_eq_mul] using mul_nonneg hc (hA.2 x)

theorem loewner_trans {A B C : Matrix n n ℝ}
    (hAB : LoewnerLE A B) (hBC : LoewnerLE B C) : LoewnerLE A C := by
  have h := hBC.add hAB
  simpa [LoewnerLE, sub_add_sub_cancel] using h

theorem loewner_congruence {A B : Matrix n n ℝ} (hAB : LoewnerLE A B)
    (T : Matrix n m ℝ) : LoewnerLE (Tᵀ * A * T) (Tᵀ * B * T) := by
  have h := hAB.conjTranspose_mul_mul_same T
  change (Tᴴ * (B - A) * T).PosSemidef at h
  simpa only [LoewnerLE, Matrix.mul_sub, Matrix.sub_mul,
    conjTranspose_eq_transpose_of_trivial] using h

/-- The PSD block inequality, expressed through an arbitrary orthogonal splitting. -/
theorem psd_pinching {M V : Matrix n n ℝ}
    (hM : M.PosSemidef) (hV : IsOrthogonalProjector V) :
    LoewnerLE M (2 • (V * M * V + (1 - V) * M * (1 - V))) := by
  have h := hM.conjTranspose_mul_mul_same (V - (1 - V))
  rw [conjTranspose_eq_transpose_of_trivial] at h
  simp only [transpose_sub, transpose_one, hV.symmetric] at h
  change (2 • (V * M * V + (1 - V) * M * (1 - V)) - M).PosSemidef
  convert h using 1 <;> noncomm_ring

theorem trace_compression {M V : Matrix n n ℝ}
    (hV : IsOrthogonalProjector V) : (V * M * V).trace = (V * M).trace := by
  rw [Matrix.trace_mul_cycle, hV.idempotent]

/-- Deterministic step of the posterior-overlap argument. `V` is the query-span
projector; `c` is the scalar bound on the hidden block. -/
theorem posterior_trace_bound {M V P : Matrix n n ℝ} {c : ℝ}
    (hM : M.PosSemidef) (hV : IsOrthogonalProjector V)
    (hP : IsOrthogonalProjector P) (hc : 0 ≤ c)
    (hbottom : LoewnerLE ((1 - V) * M * (1 - V)) (c • (1 - V))) :
    (P * M).trace ≤ 2 * (V * M).trace + 2 * c * P.trace := by
  have hpin := trace_mul_mono hP.posSemidef (psd_pinching hM hV)
  have htop : (V * M * V).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hV.symmetric]
      using hM.conjTranspose_mul_mul_same V
  have ht := projector_trace_mul_le_trace hP htop
  rw [trace_compression hV] at ht
  have hb := trace_mul_mono hP.posSemidef hbottom
  have hu := projector_overlap_le hP hV.complement
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hu hc)
  simp only [Matrix.mul_smul, mul_add, Matrix.trace_smul, Matrix.trace_add,
    smul_eq_mul, two_nsmul] at hpin
  linarith

end LowRank
