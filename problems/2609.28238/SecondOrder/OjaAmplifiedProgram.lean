import SecondOrder.OjaTrialProgram

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def preferNegative {d : ℕ} (a b : CurvatureReply d) : CurvatureReply d :=
  if curvatureTag a=true then a else b

theorem preferNegative_measurable {d : ℕ} :
    Measurable (fun w : CurvatureReply d × CurvatureReply d => preferNegative w.1 w.2) :=
  Measurable.ite ((curvatureTag_measurable.comp measurable_fst) (measurableSet_singleton true))
    measurable_fst measurable_snd

def firstNegativeVector {d : ℕ} : (n : ℕ) → (Fin n → CurvatureReply d) → CurvatureReply d
  | 0, _ => .certificate
  | n+1, rs => preferNegative (firstNegativeVector n (fun i => rs i.castSucc)) (rs (Fin.last n))

theorem firstNegativeVector_draws {A : Type} {d : ℕ} (r : A → CurvatureReply d)
    (n : ℕ) (w : Draws A n) : firstNegativeVector n (drawsVector r n w)=firstNegative r n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [firstNegativeVector,drawsVector,Fin.snoc_last,Fin.snoc_castSucc,ih]
    rfl

/-- All trials execute and are charged; the output retains the first
negative reply, matching the already analyzed amplification routine. -/
def ojaRepeatedProgram {d : ℕ} (P : Parameters) (x : Point d) (γ δ : ℝ) :
    (n : ℕ) → (Fin n → OjaTrialSeed d P γ) → OracleProgram (HvpQuery d) (Point d) (CurvatureReply d)
  | 0, _ => .done .certificate
  | n+1, ss => (ojaRepeatedProgram P x γ δ n (fun i => ss i.castSucc)).bind (fun old =>
      (ojaTrialProgram P x γ δ (ss (Fin.last n))).bind (fun new => .done (preferNegative old new)))

theorem ojaRepeatedProgram_usesExactly {d : ℕ} (P : Parameters) (x : Point d) (γ δ : ℝ)
    (n : ℕ) (ss : Fin n → OjaTrialSeed d P γ) :
    OracleProgram.UsesExactly (n*ojaTrialCallCount P d γ δ) (ojaRepeatedProgram P x γ δ n ss) := by
  induction n with
  | zero => simp only [Nat.zero_mul,ojaRepeatedProgram,OracleProgram.UsesExactly]
  | succ n ih =>
    rw [Nat.succ_mul]
    exact (ih _).bind _ (fun old =>
      (ojaTrialProgram_usesExactly P x γ δ (ss (Fin.last n))).bind (M := 0)
        (fun new => .done (preferNegative old new)) (fun _ => True.intro))

theorem ojaRepeatedProgram_measurable {d : ℕ} (P : Parameters) (γ δ : ℝ) (n : ℕ) :
    OracleProgram.MeasurableFamily (.grad 0) .certificate
      (fun w : Point d × (Fin n → OjaTrialSeed d P γ) => ojaRepeatedProgram P w.1 γ δ n w.2) := by
  induction n with
  | zero => exact OracleProgram.measurableFamily_done _ _ _ measurable_const
  | succ n ih =>
    have hp : Measurable (fun w : Point d × (Fin (n+1) → OjaTrialSeed d P γ) =>
        (w.1,fun i : Fin n => w.2 i.castSucc)) :=
      measurable_fst.prodMk (measurable_pi_lambda _ (fun i =>
        (measurable_pi_apply i.castSucc).comp measurable_snd))
    apply (ih.comp _ hp).bind
    have ht : Measurable (fun w : (Point d × (Fin (n+1) → OjaTrialSeed d P γ)) × CurvatureReply d =>
        (w.1.1,w.1.2 (Fin.last n))) := measurable_fst.fst.prodMk
      ((measurable_pi_apply (Fin.last n)).comp measurable_fst.snd)
    apply ((ojaTrialProgram_measurable (d := d) P γ δ).comp _ ht).bind
    apply OracleProgram.measurableFamily_done
    have hm : Measurable (fun w :
        ((Point d × (Fin (n+1) → OjaTrialSeed d P γ)) × CurvatureReply d) × CurvatureReply d =>
        (w.1.2,w.2)) := measurable_fst.snd.prodMk measurable_snd
    have hh := (preferNegative_measurable (d := d)).comp hm
    exact hh

/-- The repeated program starts each trial at the next fresh block. This
statement applies to every sample sequence, including exceptional replies. -/
theorem ojaRepeatedProgram_run {Ω : Type} {d : ℕ} (P : Parameters)
    (reply : HvpQuery d → Ω → Point d) (x : Point d) (γ δ : ℝ)
    (n : ℕ) (ss : Fin n → OjaTrialSeed d P γ) (rs : Fin n → CurvatureReply d) (zs : ℕ → Ω)
    (hr : ∀ i : Fin n, OracleProgram.run (.grad 0) reply
      (fun j => zs ((i:ℕ)*ojaTrialCallCount P d γ δ+j)) (ojaTrialProgram P x γ δ (ss i))
        (ojaTrialCallCount P d γ δ)=.done (rs i)) :
    OracleProgram.run (.grad 0) reply zs (ojaRepeatedProgram P x γ δ n ss)
      (n*ojaTrialCallCount P d γ δ)=.done (firstNegativeVector n rs) := by
  induction n with
  | zero => simp only [Nat.zero_mul,ojaRepeatedProgram,OracleProgram.run,firstNegativeVector]
  | succ n ih =>
    have hpre := ih (fun i => ss i.castSucc) (fun i => rs i.castSucc) (fun i => hr i.castSucc)
    have hlast := hr (Fin.last n)
    rw [Nat.succ_mul,ojaRepeatedProgram,
      OracleProgram.run_bind_of_exact (.grad 0) reply zs
        (ojaRepeatedProgram_usesExactly P x γ δ n (fun i => ss i.castSucc)) _ hpre]
    exact OracleProgram.run_bind_of_exact (.grad 0) reply
      (fun j => zs (n*ojaTrialCallCount P d γ δ+j))
      (ojaTrialProgram_usesExactly P x γ δ (ss (Fin.last n))) _ hlast 0

abbrev OjaAmplifiedSeed (d : ℕ) (P : Parameters) (γ δ : ℝ) := Fin (ojaRepeats δ) → OjaTrialSeed d P γ

def ojaAmplifiedSeedLaw (P : Parameters) {d : ℕ} (hd : 0<d) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) :
    Measure (OjaAmplifiedSeed d P γ δ) :=
  Measure.map (drawsVector id (ojaRepeats δ)) (drawsLaw (ojaTrialSeedLaw P hd hγ) (ojaRepeats δ))

instance ojaAmplifiedSeedLaw_probability (P : Parameters) {d : ℕ} (hd : 0<d)
    {γ : ℝ} (hγ : 0<γ) (δ : ℝ) : IsProbabilityMeasure (ojaAmplifiedSeedLaw P hd hγ δ) := by
  unfold ojaAmplifiedSeedLaw
  apply isProbabilityMeasure_map
  exact (drawsVector_measurable measurable_id _).aemeasurable

def ojaAmplifiedProgram {d : ℕ} (P : Parameters) (x : Point d) (γ δ : ℝ)
    (ss : OjaAmplifiedSeed d P γ δ) : OracleProgram (HvpQuery d) (Point d) (CurvatureReply d) :=
  ojaRepeatedProgram P x γ (ojaValidationFailure δ) (ojaRepeats δ) ss

theorem ojaAmplifiedProgram_usesExactly {d : ℕ} (P : Parameters) (x : Point d) (γ δ : ℝ)
    (ss : OjaAmplifiedSeed d P γ δ) :
    OracleProgram.UsesExactly (ojaAmplifiedQueryCount P d γ δ) (ojaAmplifiedProgram P x γ δ ss) := by
  unfold ojaAmplifiedQueryCount ojaAmplifiedProgram
  dsimp only [OjaAmplifiedSeed] at ss
  generalize hn : ojaRepeats δ=n at ss ⊢
  simpa only [ojaTrialCallCount] using
    ojaRepeatedProgram_usesExactly (d := d) P x γ (ojaValidationFailure δ) n ss

theorem ojaAmplifiedProgram_measurable {d : ℕ} (P : Parameters) (γ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) .certificate
      (fun w : Point d × OjaAmplifiedSeed d P γ δ => ojaAmplifiedProgram P w.1 γ δ w.2) :=
  ojaRepeatedProgram_measurable P γ (ojaValidationFailure δ) (ojaRepeats δ)

end
end SecondOrder
