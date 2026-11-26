import SecondOrder.PostMoveProgram
import SecondOrder.BranchedOjaProgram
import SecondOrder.OracleProgramCredit

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

abbrev BudgetTracker (d L : ℕ) := QueryBudgetState (TrackedState d L)
abbrev TrackingProgramSeed (d L : ℕ) (P : Parameters) (γ δ : ℝ) :=
  BranchedOjaSeed d P γ δ × Bool × PostChordSeed L δ
abbrev BudgetStepInput (d L : ℕ) (P : Parameters) (γ δ : ℝ) :=
  BudgetTracker d L × TrackingProgramSeed d L P γ δ

def requestedOjaProgram {d L : ℕ} (P : Parameters) (τ γ δ : ℝ)
    (w : TrackedState d L × BranchedOjaSeed d P γ δ) :
    OracleProgram (HvpQuery d) (Point d) (CurvatureReply d) :=
  if trackedCurvatureNeeded τ w.1 then branchedOjaProgram P w.1.physical.point γ δ w.2
  else .done .certificate

theorem requestedOjaProgram_measurable {d L : ℕ} (P : Parameters) (τ γ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) .certificate (@requestedOjaProgram d L P τ γ δ) := by
  have hz := (tracked_measurable_fields.mp
    (measurable_fst : Measurable (fun w : TrackedState d L × BranchedOjaSeed d P γ δ => w.1))).1
  have hx := (state_measurable_fields.mp hz).1
  have hp := (branchedOjaProgram_measurable P γ δ).comp _ (hx.prodMk measurable_snd)
  have hd := OracleProgram.measurableFamily_done (Y := Point d) (HvpQuery.grad (0 : Point d))
    (CurvatureReply.certificate : CurvatureReply d)
    (fun _ : TrackedState d L × BranchedOjaSeed d P γ δ => (CurvatureReply.certificate : CurvatureReply d))
    measurable_const
  have hh := hp.ite hd {w : TrackedState d L × BranchedOjaSeed d P γ δ | trackedCurvatureNeeded τ w.1}
    (trackedCurvatureNeeded_measurableSet τ measurable_fst)
  exact hh

theorem requestedOjaProgram_usesAtMost {d L : ℕ} (P : Parameters) (τ γ δ : ℝ)
    (w : TrackedState d L × BranchedOjaSeed d P γ δ) :
    OracleProgram.UsesAtMost (curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) w.1)
      (requestedOjaProgram P τ γ δ w) := by
  unfold requestedOjaProgram curvatureRequestPrice
  split_ifs
  · exact branchedOjaProgram_usesAtMost P _ γ δ _
  · trivial

/-- The entire post-move price is checked after curvature replies and
before any chord or refresh request. Rejection retains the original state. -/
def postReservationProgram {d L : ℕ} (P : Parameters) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ)
    (w : BudgetStepInput d L P γ δ) (r : CurvatureReply d) :
    OracleProgram (HvpQuery d) (Point d) (BudgetTracker d L) :=
  let c := curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) w.1.1
  let p := postRequestPrice P q Lip s τ ρ δ w.1.1 r w.2.2.1
  if w.1.2.1+c+p≤Q then
    OracleProgram.bind (postMoveProgram P q Lip s τ ρ δ (w.1.1,r,w.2.2.1,w.2.2.2))
      (fun z => .done (z,w.1.2.1+c+p,false))
  else .done (w.1.1,w.1.2.1+c,true)

theorem postReservationProgram_measurable {d L : ℕ} (P : Parameters) (q Q : ℕ)
    (Lip s τ ρ γ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) (trackedInitial 0,0,true)
      (fun u : BudgetStepInput d L P γ δ × CurvatureReply d =>
        postReservationProgram P q Q Lip s τ ρ γ δ u.1 u.2) := by
  have hc : Measurable (fun u : BudgetStepInput d L P γ δ × CurvatureReply d =>
      u.1.1.2.1+curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) u.1.1.1) :=
    measurable_fst.fst.snd.fst.add (curvatureRequestPrice_measurable τ _ measurable_fst.fst.fst)
  have hcost := hc.add (postRequestPrice_measurable P q Lip s τ ρ δ
    measurable_fst.fst.fst measurable_snd measurable_fst.snd.snd.fst)
  have hp := (postMoveProgram_measurable (d := d) (L := L) P q Lip s τ ρ δ).comp
    (fun u : BudgetStepInput d L P γ δ × CurvatureReply d =>
      (u.1.1.1,u.2,u.1.2.2.1,u.1.2.2.2))
    (measurable_fst.fst.fst.prodMk (measurable_snd.prodMk
      (measurable_fst.snd.snd.fst.prodMk measurable_fst.snd.snd.snd)))
  have hf := OracleProgram.measurableFamily_done (Y := Point d) (HvpQuery.grad (0 : Point d))
    ((trackedInitial 0,0,true) : BudgetTracker d L)
    (fun v : (BudgetStepInput d L P γ δ × CurvatureReply d) × TrackedState d L =>
      (v.2,v.1.1.1.2.1+curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) v.1.1.1.1+
        postRequestPrice P q Lip s τ ρ δ v.1.1.1.1 v.1.2 v.1.1.2.2.1,false))
    (measurable_snd.prodMk ((hcost.comp measurable_fst).prodMk measurable_const))
  have hb := hp.bind (f := fun (u : BudgetStepInput d L P γ δ × CurvatureReply d) (z : TrackedState d L) =>
    .done (z,u.1.1.2.1+curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) u.1.1.1+
      postRequestPrice P q Lip s τ ρ δ u.1.1.1 u.2 u.1.2.2.1,false)) hf
  have hd := OracleProgram.measurableFamily_done (Y := Point d) (HvpQuery.grad (0 : Point d))
    ((trackedInitial 0,0,true) : BudgetTracker d L)
    (fun u : BudgetStepInput d L P γ δ × CurvatureReply d =>
      (u.1.1.1,u.1.1.2.1+curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) u.1.1.1,true))
    (measurable_fst.fst.fst.prodMk (hc.prodMk measurable_const))
  have hh := hb.ite hd {u : BudgetStepInput d L P γ δ × CurvatureReply d |
    u.1.1.2.1+curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) u.1.1.1+
      postRequestPrice P q Lip s τ ρ δ u.1.1.1 u.2 u.1.2.2.1≤Q}
    (measurableSet_le hcost measurable_const)
  exact hh

def budgetStepProgram {d L : ℕ} (P : Parameters) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ)
    (w : BudgetStepInput d L P γ δ) : OracleProgram (HvpQuery d) (Point d) (BudgetTracker d L) :=
  if w.1.2.2 then .done w.1 else
    let c := curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) w.1.1
    if w.1.2.1+c≤Q then
      OracleProgram.bind (requestedOjaProgram P τ γ δ (w.1.1,w.2.1))
        (postReservationProgram P q Q Lip s τ ρ γ δ w)
    else .done (w.1.1,w.1.2.1,true)

theorem budgetStepProgram_measurable {d L : ℕ} (P : Parameters) (q Q : ℕ)
    (Lip s τ ρ γ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) (trackedInitial 0,0,true)
      (@budgetStepProgram d L P q Q Lip s τ ρ γ δ) := by
  have hc : Measurable (fun w : BudgetStepInput d L P γ δ =>
      w.1.2.1+curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) w.1.1) :=
    measurable_fst.snd.fst.add (curvatureRequestPrice_measurable τ _ measurable_fst.fst)
  have hp := (requestedOjaProgram_measurable (d := d) (L := L) P τ γ δ).comp
    (fun w : BudgetStepInput d L P γ δ => (w.1.1,w.2.1)) (measurable_fst.fst.prodMk measurable_snd.fst)
  have hb := hp.bind (postReservationProgram_measurable P q Q Lip s τ ρ γ δ)
  have hd := OracleProgram.measurableFamily_done (Y := Point d) (HvpQuery.grad (0 : Point d))
    ((trackedInitial 0,0,true) : BudgetTracker d L)
    (fun w : BudgetStepInput d L P γ δ => (w.1.1,w.1.2.1,true))
    (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_const))
  have hi := hb.ite hd {w : BudgetStepInput d L P γ δ |
    w.1.2.1+curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) w.1.1≤Q}
    (measurableSet_le hc measurable_const)
  have hf := OracleProgram.measurableFamily_done (Y := Point d) (HvpQuery.grad (0 : Point d))
    ((trackedInitial 0,0,true) : BudgetTracker d L)
    (fun w : BudgetStepInput d L P γ δ => w.1) measurable_fst
  have hh := hf.ite hi {w : BudgetStepInput d L P γ δ | w.1.2.2=true}
    (measurable_fst.snd.snd (measurableSet_singleton true))
  exact hh

theorem postReservationProgram_credit {d L : ℕ} (P : Parameters) (q Q : ℕ)
    (Lip s τ ρ γ δ : ℝ) (w : BudgetStepInput d L P γ δ) (r : CurvatureReply d) :
    OracleProgram.UsesWithCredit
      (Q-w.1.2.1-curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) w.1.1)
      (postReservationProgram P q Q Lip s τ ρ γ δ w r) (fun z => Q-z.2.1) := by
  unfold postReservationProgram
  dsimp only
  split_ifs with hc
  · have hp := (postMoveProgram_usesExactly P q Lip s τ ρ δ (w.1.1,r,w.2.2.1,w.2.2.2)).usesAtMost
    dsimp only at hp
    have hh := OracleProgram.usesAtMost_bind_credit hp
      (fun z => .done (z,w.1.2.1+curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) w.1.1+
        postRequestPrice P q Lip s τ ρ δ w.1.1 r w.2.2.1,false))
      (fun z : BudgetTracker d L => Q-z.2.1)
      (m := Q-(w.1.2.1+curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) w.1.1+
        postRequestPrice P q Lip s τ ρ δ w.1.1 r w.2.2.1)) (fun _ => Nat.le_refl _)
    exact hh.mono (by omega)
  · change Q-(w.1.2.1+curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) w.1.1)≤_
    omega

/-- The program reserves enough credit for every future step. This bound
holds for arbitrary replies and seeds, including zero-mass seed branches. -/
theorem budgetStepProgram_credit {d L : ℕ} (P : Parameters) (q Q : ℕ)
    (Lip s τ ρ γ δ : ℝ) (w : BudgetStepInput d L P γ δ) :
    OracleProgram.UsesWithCredit (Q-w.1.2.1)
      (budgetStepProgram P q Q Lip s τ ρ γ δ w) (fun z => Q-z.2.1) := by
  unfold budgetStepProgram
  dsimp only
  split_ifs with hf hc
  · exact Nat.le_refl _
  · have hp := requestedOjaProgram_usesAtMost P τ γ δ (w.1.1,w.2.1)
    dsimp only at hp
    have hh := OracleProgram.usesAtMost_bind_credit hp
      (postReservationProgram P q Q Lip s τ ρ γ δ w) (fun z => Q-z.2.1)
      (fun r => postReservationProgram_credit P q Q Lip s τ ρ γ δ w r)
    exact hh.mono (by omega)
  · exact Nat.le_refl _

end
end SecondOrder
