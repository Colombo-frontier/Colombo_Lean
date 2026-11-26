import LowRank.CappedProjectorExtension

/-! Deterministically complete a rank-at-most-k projector to rank exactly k
by trying the standard axes in order. The entire completion map is measurable. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def coordinateAxis (d n : ℕ) : Fin d → ℝ := fun i => if i.val = n then 1 else 0

theorem coordinateAxis_eq_single {d : ℕ} (i : Fin d) :
    coordinateAxis d i.val = Pi.single i 1 := by
  ext j
  simp [coordinateAxis, Pi.single_apply, Fin.ext_iff]

def completeProjectorPrefix {d : ℕ} (k : ℕ) (P : Matrix (Fin d) (Fin d) ℝ) :
    ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => P
  | n + 1 => cappedProjectorExtension k (completeProjectorPrefix k P n) (coordinateAxis d n)

def completeProjector {d : ℕ} (k : ℕ) (P : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ := completeProjectorPrefix k P d

theorem completeProjectorPrefix_isProjector {d : ℕ} (k : ℕ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) (n : ℕ) :
    IsOrthogonalProjector (completeProjectorPrefix k P n) := by
  induction n with
  | zero => exact hP
  | succ n ih => exact cappedProjectorExtension_isProjector ih _

theorem completeProjectorPrefix_rank_le {d k : ℕ}
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) (hrank : P.rank ≤ k) (n : ℕ) :
    (completeProjectorPrefix k P n).rank ≤ k := by
  induction n with
  | zero => exact hrank
  | succ n ih => exact cappedProjectorExtension_rank_le (completeProjectorPrefix_isProjector k hP n) ih _

theorem completeProjectorPrefix_mul_original {d : ℕ} (k : ℕ)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) (n : ℕ) :
    completeProjectorPrefix k P n * P = P := by
  induction n with
  | zero => exact hP.idempotent
  | succ n ih =>
    calc
      _ = completeProjectorPrefix k P (n + 1) * (completeProjectorPrefix k P n * P) := by rw [ih]
      _ = P := by
        rw [← Matrix.mul_assoc, completeProjectorPrefix,
          cappedProjectorExtension_mul_original (completeProjectorPrefix_isProjector k hP n), ih]

theorem completeProjectorPrefix_fixes_axes {d k : ℕ}
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) (n : ℕ)
    (ht : (completeProjectorPrefix k P n).trace < (k : ℝ))
    (i : Fin d) (hi : i.val < n) :
    completeProjectorPrefix k P n *ᵥ Pi.single i 1 = Pi.single i 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    have htprev : (completeProjectorPrefix k P n).trace < (k : ℝ) :=
      (cappedProjectorExtension_trace_ge _ _).trans_lt ht
    have hQ := completeProjectorPrefix_isProjector k hP n
    obtain hlt | heq := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
    · exact cappedProjectorExtension_fixes_original hQ _ _ (ih htprev hlt)
    · have h := cappedProjectorExtension_fixes_new hQ htprev (coordinateAxis d n)
      have haxis : coordinateAxis d n = Pi.single i 1 := by
        rw [← heq, coordinateAxis_eq_single]
      rw [haxis] at h
      simpa only [completeProjectorPrefix, haxis] using h

theorem completeProjector_spec {d k : ℕ} (hk : k ≤ d)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P) (hrank : P.rank ≤ k) :
    IsOrthogonalProjector (completeProjector k P) ∧ (completeProjector k P).rank = k ∧
      completeProjector k P * P = P := by
  have hQ := completeProjectorPrefix_isProjector k hP d
  have hr := completeProjectorPrefix_rank_le hP hrank d
  refine ⟨hQ, ?_, completeProjectorPrefix_mul_original k hP d⟩
  apply le_antisymm hr
  by_contra hnot
  have hlt : (completeProjectorPrefix k P d).rank < k := Nat.lt_of_not_ge hnot
  have ht : (completeProjectorPrefix k P d).trace < (k : ℝ) := by
    rw [hQ.trace_eq_rank]
    exact_mod_cast hlt
  have hone : completeProjectorPrefix k P d = 1 := by
    ext i j
    have h := congrFun (completeProjectorPrefix_fixes_axes hP d ht j j.isLt) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h
  rw [hone, Matrix.rank_one, Fintype.card_fin] at hlt
  omega

theorem measurable_completeProjectorPrefix (d k n : ℕ) : Measurable
    (fun P : Matrix (Fin d) (Fin d) ℝ => completeProjectorPrefix k P n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
    exact (measurable_cappedProjectorExtension d k).comp (ih.prodMk measurable_const)

theorem measurable_completeProjector (d k : ℕ) : Measurable
    (completeProjector k : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ) :=
  measurable_completeProjectorPrefix d k d

end
end LowRank
