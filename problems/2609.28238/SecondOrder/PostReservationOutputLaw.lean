import SecondOrder.PostMoveOutputLaw
import SecondOrder.SeedProductLaw

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def sampledPostReservation {Ω : Type} {d L : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (q Q κ : ℕ) (Lip s τ ρ δ : ℝ) (z : BudgetTracker d L) (r : CurvatureReply d) (b : Bool)
    (w : PostMoveTape Ω P L τ δ) : BudgetTracker d L :=
  let c := curvatureRequestPrice τ κ z.1
  let p := postRequestPrice P q Lip s τ ρ δ z.1 r b
  if z.2.1+c+p≤Q then (sampledPostStep P f q Lip s τ ρ δ z.1 r b w,z.2.1+c+p,false)
  else (z.1,z.2.1+c,true)

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d L : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.sampledPostReservation_measurable (h : CommonLoss μ P ν F f)
    {A : Type} [MeasurableSpace A] (q Q κ : ℕ) (Lip s τ ρ δ : ℝ)
    {z : A → BudgetTracker d L} {r : A → CurvatureReply d} {b : A → Bool}
    {w : A → PostMoveTape Ω P L τ δ} (hz : Measurable z) (hr : Measurable r)
    (hb : Measurable b) (hw : Measurable w) :
    Measurable (fun a => sampledPostReservation P f q Q κ Lip s τ ρ δ (z a) (r a) (b a) (w a)) := by
  have hc := hz.snd.fst.add (curvatureRequestPrice_measurable τ κ hz.fst)
  have hp := hc.add (postRequestPrice_measurable P q Lip s τ ρ δ hz.fst hr hb)
  have ht := h.sampledPostStep_measurable q Lip s τ ρ δ hz.fst hr hb hw
  exact (ht.prodMk (hp.prodMk measurable_const)).ite (measurableSet_le hp measurable_const)
    (hz.fst.prodMk (hc.prodMk measurable_const))

/-- The reservation reads no rejected post-move batch. The auxiliary
execution horizon Q is reduced to the actual price on accepted branches. -/
theorem CommonLoss.postReservationProgram_slice_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ) (z : BudgetTracker d L)
    (r : CurvatureReply d) (b : Bool) (os : BranchedOjaSeed d P γ δ) :
    OracleProgram.seededOutputLaw μ (postChordSeedLaw L δ) (.grad 0) (trackedInitial 0,0,true)
      (fun q a => hvpReply f a q)
      (fun seeds => postReservationProgram P q Q Lip s τ ρ γ δ (z,os,b,seeds) r) Q=
      Measure.map (sampledPostReservation P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ z r b)
        (postMoveLaw μ P L τ δ) := by
  let c := curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) z.1
  let price := postRequestPrice P q Lip s τ ρ δ z.1 r b
  by_cases hc : z.2.1+c+price≤Q
  · let g := fun u : TrackedState d L => ((u,z.2.1+c+price,false) : BudgetTracker d L)
    have hg : Measurable g := measurable_id.prodMk measurable_const
    let p := fun seeds => postMoveProgram P q Lip s τ ρ δ (z.1,r,b,seeds)
    have hp : OracleProgram.MeasurableFamily (.grad 0) (trackedInitial 0) p :=
      (postMoveProgram_measurable P q Lip s τ ρ δ).comp
        (fun seeds => (z.1,r,b,seeds))
        (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    have hN : ∀ seeds, OracleProgram.UsesAtMost price (p seeds) := by
      intro seeds
      exact (postMoveProgram_usesExactly P q Lip s τ ρ δ (z.1,r,b,seeds)).usesAtMost
    have hf := hp.bind (f := fun _ u => (OracleProgram.done (g u) :
      OracleProgram (HvpQuery d) (Point d) (BudgetTracker d L)))
      (OracleProgram.measurableFamily_done (Y := Point d) (HvpQuery.grad (0 : Point d))
        ((trackedInitial 0,0,true) : BudgetTracker d L)
        (fun w : PostChordSeed L δ × TrackedState d L => g w.2) (hg.comp measurable_snd))
    have hb : ∀ seeds, OracleProgram.UsesAtMost price
        (OracleProgram.bind (p seeds) (fun u => .done (g u))) := by
      intro seeds
      have hh := OracleProgram.usesAtMost_bind (hN seeds) (fun u => .done (g u))
        (m := 0) (fun _ => trivial)
      simpa only [Nat.add_zero] using hh
    have he : (fun seeds => postReservationProgram P q Q Lip s τ ρ γ δ (z,os,b,seeds) r)=
        (fun seeds => OracleProgram.bind (p seeds) (fun u => .done (g u))) := by
      funext seeds
      exact if_pos hc
    rw [he,OracleProgram.seededOutputLaw_of_budget_le μ (postChordSeedLaw L δ)
      (.grad 0) 0 ((trackedInitial 0,0,true) : BudgetTracker d L) a₀ (fun q a => hvpReply f a q)
      h.hvpReply_joint_measurable _ hf price hb Q (by omega),
      OracleProgram.seededOutputLaw_bind_done μ (postChordSeedLaw L δ) (.grad 0) 0 (trackedInitial 0)
        ((trackedInitial 0,0,true) : BudgetTracker d L) a₀ (fun q a => hvpReply f a q)
        h.hvpReply_joint_measurable p hp price hN g hg,
      h.postMoveProgram_outputLaw a₀ q Lip s τ ρ δ z.1 r b]
    have ht : Measurable (sampledPostStep P f q Lip s τ ρ δ z.1 r b) :=
      h.sampledPostStep_measurable q Lip s τ ρ δ
        measurable_const measurable_const measurable_const measurable_id
    rw [Measure.map_map hg ht]
    apply congrArg (fun k : PostMoveTape Ω P L τ δ → BudgetTracker d L =>
      Measure.map k (postMoveLaw μ P L τ δ))
    funext w
    exact (if_pos hc).symm
  · have he : (fun seeds => postReservationProgram P q Q Lip s τ ρ γ δ (z,os,b,seeds) r)=
        (fun _ : PostChordSeed L δ => .done ((z.1,z.2.1+c,true) : BudgetTracker d L)) := by
      funext seeds
      exact if_neg hc
    have ht : sampledPostReservation P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ z r b=
        (fun _ : PostMoveTape Ω P L τ δ => ((z.1,z.2.1+c,true) : BudgetTracker d L)) := by
      funext w
      exact if_neg hc
    rw [he,ht,OracleProgram.seededOutputLaw_done]
    simp

end
end SecondOrder
