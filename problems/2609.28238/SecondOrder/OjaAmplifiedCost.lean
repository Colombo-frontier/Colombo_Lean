import SecondOrder.OjaAmplification

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

def rayleighTrace {Ω : Type*} {d : ℕ} (P : Parameters) (x v : Point d) (ρ δ : ℝ)
    (w : LocalDraws Ω (P.hessianBound^2) ρ δ) : List (Ω × HvpQuery d) :=
  List.ofFn (fun i => rayleighSampleCall P x v ρ δ w ((Fintype.equivFin (RayleighSlot P ρ δ)).symm i))

theorem rayleighTrace_length {Ω : Type*} {d : ℕ} (P : Parameters) (x v : Point d) (ρ δ : ℝ)
    (w : LocalDraws Ω (P.hessianBound^2) ρ δ) :
    (rayleighTrace P x v ρ δ w).length = localQueryCount (P.hessianBound^2) ρ δ := by
  simp only [rayleighTrace, List.length_ofFn, rayleighSampleCall_count]

theorem rayleighSampleCall_mem_trace {Ω : Type*} {d : ℕ} (P : Parameters) (x v : Point d) (ρ δ : ℝ)
    (w : LocalDraws Ω (P.hessianBound^2) ρ δ) (i : RayleighSlot P ρ δ) :
    rayleighSampleCall P x v ρ δ w i ∈ rayleighTrace P x v ρ δ w := by
  apply List.mem_ofFn.mpr
  exact ⟨Fintype.equivFin (RayleighSlot P ρ δ) i, by simp⟩

def ojaTrialTrace {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) (w : OjaTrialDraws Ω d P γ δ) : List (Ω × HvpQuery d) :=
  ojaCandidateTrace P f (ojaLearningRate d (ojaCurvatureTolerance P γ)) x
    (ojaIterationCount d (ojaCurvatureTolerance P γ)) w.1 ++
      rayleighTrace P x (ojaTrialCandidate P f x γ w.1) (γ/8) δ w.2

theorem ojaTrialTrace_length {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) (w : OjaTrialDraws Ω d P γ δ) :
    (ojaTrialTrace P f x γ δ w).length = ojaIterationCount d (ojaCurvatureTolerance P γ) +
      localQueryCount (P.hessianBound^2) (γ/8) δ := by
  simp only [ojaTrialTrace, List.length_append, ojaCandidateTrace_length, rayleighTrace_length]

/-- The sampling schedule performs all trials, so its deterministic price
also covers runs in which an early trial already provides the output. -/
def ojaRepeatedTrace {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) : (n : ℕ) → Draws (OjaTrialDraws Ω d P γ δ) n → List (Ω × HvpQuery d)
  | 0, _ => []
  | n+1, w => ojaRepeatedTrace P f x γ δ n w.1 ++ ojaTrialTrace P f x γ δ w.2

theorem ojaRepeatedTrace_length {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) (n : ℕ) (w : Draws (OjaTrialDraws Ω d P γ δ) n) :
    (ojaRepeatedTrace P f x γ δ n w).length = n*(ojaIterationCount d (ojaCurvatureTolerance P γ) +
      localQueryCount (P.hessianBound^2) (γ/8) δ) := by
  induction n with
  | zero => simp [ojaRepeatedTrace]
  | succ n ih => simp only [ojaRepeatedTrace, List.length_append, ih, ojaTrialTrace_length]; ring

def ojaAmplifiedQueryCount (P : Parameters) (d : ℕ) (γ δ : ℝ) : ℕ :=
  ojaRepeats δ * (ojaIterationCount d (ojaCurvatureTolerance P γ) +
    localQueryCount (P.hessianBound^2) (γ/8) (ojaValidationFailure δ))

def ojaAmplifiedTrace {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) (w : OjaAmplifiedDraws Ω d P γ δ) : List (Ω × HvpQuery d) :=
  ojaRepeatedTrace P f x γ (ojaValidationFailure δ) (ojaRepeats δ) w

theorem ojaAmplifiedTrace_length {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (x : Point d) (γ δ : ℝ) (w : OjaAmplifiedDraws Ω d P γ δ) :
    (ojaAmplifiedTrace P f x γ δ w).length = ojaAmplifiedQueryCount P d γ δ :=
  ojaRepeatedTrace_length P f x γ (ojaValidationFailure δ) (ojaRepeats δ) w

theorem ojaAmplifiedQueryCount_bound (P : Parameters) {d : ℕ} (hd : 0 < d)
    {γ δ : ℝ} (hγ : 0 < γ) (hγB : γ ≤ 4*eigenHessianBound P) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (ojaAmplifiedQueryCount P d γ δ : ℝ) ≤ (ojaRepeats δ:ℝ) *
      (104976*(eigenHessianBound P)^2*(1+Real.log (4*(d:ℝ)))^2/γ^2 +
        (2304*P.hessianBound^2/γ^2+2)*(8*Real.log (1/ojaValidationFailure δ)+2)) := by
  have hB := eigenHessianBound_pos P
  have hε := ojaCurvatureTolerance_pos P hγ
  have hε1 : ojaCurvatureTolerance P γ ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*eigenHessianBound P)).mpr
    simpa using hγB
  have hN : (ojaIterationCount d (ojaCurvatureTolerance P γ):ℝ) ≤
      104976*(eigenHessianBound P)^2*(1+Real.log (4*(d:ℝ)))^2/γ^2 := by
    convert ojaIterationCount_bound hd hε hε1 using 1
    unfold ojaCurvatureTolerance
    field_simp
    ring
  have hv := rayleighValidation_query_bound P γ (ojaValidationFailure_pos hδ)
    (le_trans (ojaValidationFailure_le hδ1) (by norm_num : (1:ℝ)/192 ≤ 1))
  unfold ojaAmplifiedQueryCount
  push_cast
  exact mul_le_mul_of_nonneg_left (add_le_add hN hv) (Nat.cast_nonneg _)

end
end SecondOrder
