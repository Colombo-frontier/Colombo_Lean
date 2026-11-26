import SecondOrder.ExactOracleProgram
import SecondOrder.HvpAlgorithmSimulation

open MeasureTheory

namespace SecondOrder
noncomputable section

abbrev OjaTrajectoryResult (d N : ℕ) := Point d × (Fin N → Point d)

def ojaTrajectoryProgram {d : ℕ} (P : Parameters) (η : ℝ) (x v : Point d) :
    (N : ℕ) → OracleProgram (HvpQuery d) (Point d) (OjaTrajectoryResult d N)
  | 0 => .done (v,Fin.elim0)
  | N+1 => (ojaTrajectoryProgram P η x v N).bind (fun s =>
      .request (.hvp x s.1) (fun r => .done (ojaStepFromHvp P η s.1 r,Fin.snoc s.2 s.1)))

theorem ojaStepFromHvp_measurable {d : ℕ} (P : Parameters) (η : ℝ) :
    Measurable (fun w : Point d × Point d => ojaStepFromHvp P η w.1 w.2) := by
  exact normalizeProbe_measurable.comp
    (measurable_fst.add (((measurable_fst.const_smul (eigenHessianBound P)).sub measurable_snd).const_smul
      ((2*eigenHessianBound P)⁻¹) |>.const_smul η))

theorem ojaTrajectoryProgram_usesExactly {d : ℕ} (P : Parameters) (η : ℝ) (x v : Point d) (N : ℕ) :
    OracleProgram.UsesExactly N (ojaTrajectoryProgram P η x v N) := by
  induction N with
  | zero => trivial
  | succ N ih =>
    exact ih.bind _ (fun s y => True.intro)

theorem ojaTrajectoryProgram_measurable {d : ℕ} (P : Parameters) (η : ℝ) (N : ℕ) :
    OracleProgram.MeasurableFamily (.grad 0) (0,fun _ => 0)
      (fun w : Point d × Point d => ojaTrajectoryProgram P η w.1 w.2 N) := by
  induction N with
  | zero =>
    apply OracleProgram.measurableFamily_done
    exact measurable_snd.prodMk (measurable_pi_lambda _ (fun i => Fin.elim0 i))
  | succ N ih =>
    apply ih.bind
    apply OracleProgram.measurableFamily_request
    · exact (hvpQueryMeasurableEquiv d).symm.measurable.comp
        (measurable_inr.comp (measurable_fst.fst.prodMk measurable_snd.fst))
    · apply OracleProgram.measurableFamily_done
      have hv : Measurable (fun w : ((Point d × Point d) × OjaTrajectoryResult d N) × Point d =>
          w.1.2.1) := measurable_fst.snd.fst
      have hr : Measurable (fun w : ((Point d × Point d) × OjaTrajectoryResult d N) × Point d =>
          w.2) := measurable_snd
      have hp := hv.prodMk hr
      have hm := (ojaStepFromHvp_measurable (d := d) P η).comp hp
      have hs : Measurable (fun w : ((Point d × Point d) × OjaTrajectoryResult d N) × Point d =>
          (Fin.snoc w.1.2.2 w.1.2.1 : Fin (N+1) → Point d)) := by
        apply measurable_pi_lambda
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using hv
        · simpa only [Fin.snoc_castSucc] using
            ((measurable_pi_apply j).comp measurable_fst.snd.snd :
              Measurable (fun w : ((Point d × Point d) × OjaTrajectoryResult d N) × Point d => w.1.2.2 j))
      exact hm.prodMk hs

/-- The exact old iterate and every pre-query direction are reproduced from
the same fresh sample sequence, for arbitrary scalar losses. -/
theorem ojaTrajectoryProgram_run {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) (N : ℕ) (w : Draws Ω N) (zs : ℕ → Ω)
    (hz : ∀ i : Fin N, zs i=drawsVector id N w i) :
    OracleProgram.run (.grad 0) (fun q z => hvpReply f z q) zs (ojaTrajectoryProgram P η x v N) N=
      .done (ojaHvpRun P f η x v N w,ojaDirections P f η x v N w) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hz' : ∀ i : Fin N, zs i=drawsVector id N w.1 i := by
      intro i
      simpa only [drawsVector,Fin.snoc_castSucc] using hz i.castSucc
    have hlast : zs N=w.2 := by
      simpa only [drawsVector,Fin.snoc_last,id_eq] using hz (Fin.last N)
    have hrun := ih w.1 hz'
    rw [ojaTrajectoryProgram,OracleProgram.run_bind_of_exact (.grad 0) _ zs
      (ojaTrajectoryProgram_usesExactly P η x v N) _ hrun 1]
    simp only [OracleProgram.run,OracleProgram.advance,OracleProgram.query,Nat.add_zero,hlast]
    rfl

def ojaCandidateProgram {d : ℕ} (P : Parameters) (η : ℝ) (x : Point d)
    (N : ℕ) (b : Fin d → Bool) (i : Fin N) : OracleProgram (HvpQuery d) (Point d) (Point d) :=
  (ojaTrajectoryProgram P η x (rademacherInit b) N).bind (fun s => .done (s.2 i))

theorem ojaCandidateProgram_usesExactly {d : ℕ} (P : Parameters) (η : ℝ) (x : Point d)
    (N : ℕ) (b : Fin d → Bool) (i : Fin N) :
    OracleProgram.UsesExactly N (ojaCandidateProgram P η x N b i) := by
  exact (ojaTrajectoryProgram_usesExactly P η x (rademacherInit b) N).bind
    (M := 0) (fun s => .done (s.2 i)) (fun _ => True.intro)

theorem ojaCandidateProgram_measurable {d : ℕ} (P : Parameters) (η : ℝ) (N : ℕ) :
    OracleProgram.MeasurableFamily (.grad 0) 0
      (fun w : Point d × ((Fin d → Bool) × Fin N) => ojaCandidateProgram P η w.1 N w.2.1 w.2.2) := by
  have hinit : Measurable (fun w : Point d × ((Fin d → Bool) × Fin N) => (w.1,rademacherInit w.2.1)) :=
    measurable_fst.prodMk ((measurable_of_finite rademacherInit).comp measurable_snd.fst)
  apply ((ojaTrajectoryProgram_measurable P η N).comp _ hinit).bind
  apply OracleProgram.measurableFamily_done
  have he : Measurable (fun w : (Fin N → Point d) × Fin N => w.1 w.2) :=
    measurable_from_prod_countable (fun i => measurable_pi_apply i)
  exact he.comp (measurable_snd.snd.prodMk measurable_fst.snd.snd)

theorem ojaCandidateProgram_run {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x : Point d) (N : ℕ)
    (w : (Draws Ω N × (Fin d → Bool)) × Fin N) (zs : ℕ → Ω)
    (hz : ∀ i : Fin N, zs i=drawsVector id N w.1.1 i) :
    OracleProgram.run (.grad 0) (fun q z => hvpReply f z q) zs
      (ojaCandidateProgram P η x N w.1.2 w.2) N=.done (ojaCandidate P f η x N w) := by
  exact OracleProgram.run_bind_of_exact (.grad 0) _ zs
    (ojaTrajectoryProgram_usesExactly P η x (rademacherInit w.1.2) N) _
    (ojaTrajectoryProgram_run P f η x (rademacherInit w.1.2) N w.1.1 zs hz) 0

end
end SecondOrder
