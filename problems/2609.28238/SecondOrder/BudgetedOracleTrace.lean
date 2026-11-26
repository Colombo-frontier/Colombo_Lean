import SecondOrder.FiniteBudgetCoupling

open scoped Classical

namespace SecondOrder
noncomputable section

/-- Enumerate every slot once. Enumeration itself does not inspect replies. -/
def oracleSlotTrace {S E : Type*} [Fintype S] (call : S → E) : List E :=
  List.ofFn (fun i => call ((Fintype.equivFin S).symm i))

theorem oracleSlotTrace_length {S E : Type*} [Fintype S] (call : S → E) :
    (oracleSlotTrace call).length = Fintype.card S := List.length_ofFn

theorem oracleSlotTrace_mem {S E : Type*} [Fintype S] (call : S → E) (i : S) :
    call i ∈ oracleSlotTrace call := List.mem_ofFn.mpr ⟨Fintype.equivFin S i, by simp⟩

def anchorOracleTrace {Ω : Type*} {d : ℕ} (P : Parameters) (x : Point d) (ρ δ : ℝ)
    (a : LocalDraws Ω (P.gradientNoise^2) ρ δ) : List (Ω × HvpQuery d) :=
  oracleSlotTrace (anchorSampleCall P x ρ δ a)

theorem anchorOracleTrace_length {Ω : Type*} {d : ℕ} (P : Parameters) (x : Point d) (ρ δ : ℝ)
    (a : LocalDraws Ω (P.gradientNoise^2) ρ δ) :
    (anchorOracleTrace P x ρ δ a).length = localQueryCount (P.gradientNoise^2) ρ δ := by
  rw [anchorOracleTrace, oracleSlotTrace_length, anchorSampleCall_count]

def postOracleTrace {Ω : Type*} {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) (w : PostMoveTape Ω P L τ δ) :
    List (Ω × HvpQuery d) :=
  oracleSlotTrace (postChordCall P Lip s τ ρ δ z r b w.1) ++
    oracleSlotTrace (postRefreshCall P q Lip s τ δ z r b w.2)

theorem postOracleTrace_length {Ω : Type*} {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) (w : PostMoveTape Ω P L τ δ) :
    (postOracleTrace P q Lip s τ ρ δ z r b w).length = postRequestPrice P q Lip s τ ρ δ z r b := by
  rw [postOracleTrace, List.length_append, oracleSlotTrace_length, oracleSlotTrace_length,
    postRequestPrice_eq_oracle_slots]

def requestedCurvatureTrace {Ω Ψ : Type*} {d L : ℕ} (τ : ℝ)
    (trace : Point d → Ψ → List (Ω × HvpQuery d)) (z : TrackedState d L) (w : Ψ) :
    List (Ω × HvpQuery d) :=
  if trackedCurvatureNeeded τ z then trace z.physical.point w else []

theorem requestedCurvatureTrace_length_le {Ω Ψ : Type*} {d L : ℕ} (τ : ℝ) (κ : ℕ)
    (trace : Point d → Ψ → List (Ω × HvpQuery d)) (ht : ∀ x w, (trace x w).length ≤ κ)
    (z : TrackedState d L) (w : Ψ) :
    (requestedCurvatureTrace τ trace z w).length ≤ curvatureRequestPrice τ κ z := by
  unfold requestedCurvatureTrace curvatureRequestPrice
  split_ifs
  · exact ht _ _
  · rfl

/-- Mirror both budget checks: a rejected post-move block contributes no
chord or refresh queries; a rejected curvature reservation contributes none. -/
def budgetedOracleStepTrace {Ω Ψ : Type*} {d L : ℕ} (P : Parameters)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (trace : Point d → Ψ → List (Ω × HvpQuery d))
    (z : QueryBudgetState (TrackedState d L)) (b : Bool) (w : TrackingStepTape Ω Ψ P L τ δ) :
    List (Ω × HvpQuery d) :=
  if z.2.2 then [] else
    let c := curvatureRequestPrice τ κ z.1
    if z.2.1+c ≤ Q then
      let r := sampledCurvature τ routine z.1 w.1
      let p := postRequestPrice P q Lip s τ ρ δ z.1 r b
      requestedCurvatureTrace τ trace z.1 w.1 ++
        if z.2.1+c+p ≤ Q then postOracleTrace P q Lip s τ ρ δ z.1 r b w.2 else []
    else []

theorem budgetedOracleStepTrace_price {Ω Ψ : Type*} {d L : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    (routine : Point d → Ψ → CurvatureReply d) (trace : Point d → Ψ → List (Ω × HvpQuery d))
    (ht : ∀ x w, (trace x w).length ≤ κ)
    (z : QueryBudgetState (TrackedState d L)) (b : Bool) (w : TrackingStepTape Ω Ψ P L τ δ) :
    (budgetedOracleStepTrace P q Q κ Lip s τ ρ δ routine trace z b w).length+z.2.1 ≤
      (budgetedTrackedStep P f q Q κ Lip s τ ρ δ routine z b w).2.1 := by
  have hc := requestedCurvatureTrace_length_le τ κ trace ht z.1 w.1
  have hp := postOracleTrace_length P q Lip s τ ρ δ z.1 (sampledCurvature τ routine z.1 w.1) b w.2
  dsimp only [budgetedOracleStepTrace, budgetedTrackedStep]
  split_ifs <;> simp only [List.length_nil, List.length_append, hp] <;> omega

def budgetedOracleRunTrace {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (trace : Point d → Ψ → List (Ω × HvpQuery d))
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) (β : ℕ → Bool) :
    (N : ℕ) → Draws (TrackingStepTape Ω Ψ P L τ δ) N → List (Ω × HvpQuery d)
  | 0, _ => if localQueryCount (P.gradientNoise^2) (τ/4) δ ≤ Q then anchorOracleTrace P 0 (τ/4) δ a else []
  | N+1, w => budgetedOracleRunTrace P f q Q κ Lip s τ ρ δ routine trace a β N w.1 ++
      budgetedOracleStepTrace P q Q κ Lip s τ ρ δ routine trace
        (budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine a β N w.1) (β N) w.2

theorem budgetedOracleRunTrace_price {Ω Ψ : Type*} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) (routine : Point d → Ψ → CurvatureReply d)
    (trace : Point d → Ψ → List (Ω × HvpQuery d)) (ht : ∀ x w, (trace x w).length ≤ κ)
    (a : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) (β : ℕ → Bool)
    (N : ℕ) (w : Draws (TrackingStepTape Ω Ψ P L τ δ) N) :
    (budgetedOracleRunTrace P f q Q κ Lip s τ ρ δ routine trace a β N w).length ≤
      (budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine a β N w).2.1 := by
  induction N with
  | zero =>
    unfold budgetedOracleRunTrace budgetedTrackedRun budgetedTrackedInitial
    split_ifs <;> simp [anchorOracleTrace_length]
  | succ N ih =>
    have hs := budgetedOracleStepTrace_price P f q Q κ Lip s τ ρ δ routine trace ht
      (budgetedTrackedRun P f q Q κ Lip s τ ρ δ routine a β N w.1) (β N) w.2
    rw [budgetedOracleRunTrace, List.length_append, budgetedTrackedRun]
    have hn := ih w.1
    omega

end
end SecondOrder
