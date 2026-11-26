import Bilevel.PolishedHistoryStationaryStopping
import Bilevel.BorelAdaptiveChannelTransport

/-! Measurable changes of query and response coordinates preserve the exact
history-dependent execution kernel on the same algorithm/oracle states.
Consequently the complete trajectory and first-halt experiment are unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory
set_option autoImplicit false
variable {S Q O Q' O' Y H : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Q'] [MeasurableSpace O']
  [MeasurableSpace Y] [MeasurableSpace H]
variable (A : BorelAdaptive.Program S Q O Y) (R : HistoryProgram.Oracle Q O H)
  (eq : Q → Q') (dq : Q' → Q) (eo : O → O') (dobs : O' → O)
  (heq : Measurable eq) (hdq : Measurable dq) (heo : Measurable eo) (hdo : Measurable dobs)

def recodeOracle : HistoryProgram.Oracle Q' O' H where
  law := (R.law.comap (fun z : Q' × H => (dq z.1,z.2))
    ((hdq.comp measurable_fst).prodMk measurable_snd)).map eo
  markov := Kernel.IsMarkovKernel.map _ heo
  update := fun z => R.update ((dq z.1.1,z.1.2),dobs z.2)
  update_measurable := R.update_measurable.comp
    (((hdq.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk (hdo.comp measurable_snd))

theorem recodeOracle_law (q : Q') (h : H) :
    (recodeOracle R dq eo dobs hdq heo hdo).law (q,h)=(R.law (dq q,h)).map eo := by
  rw [recodeOracle,Kernel.map_apply _ heo,Kernel.comap_apply]

variable (hQ : ∀ q,dq (eq q)=q) (hO : ∀ o,dobs (eo o)=o)

include hQ hO in
theorem channel_step_kernel :
    HistoryProgram.step (BorelAdaptive.channelProgram A eq dobs heq hdo)
      (recodeOracle R dq eo dobs hdq heo hdo)=HistoryProgram.step A R := by
  apply Kernel.ext
  rintro ⟨s,h⟩
  cases hh : A.halt s with
  | true =>
      rw [HistoryProgram.step_halted _ _ _ hh,HistoryProgram.step_halted _ _ _ hh]
  | false =>
      rw [HistoryProgram.step_live _ _ _ hh,HistoryProgram.step_live _ _ _ hh]
      have hm : Measurable (fun o : O' => HistoryProgram.advance
          (BorelAdaptive.channelProgram A eq dobs heq hdo)
          (recodeOracle R dq eo dobs hdq heo hdo) ((s,h),o)) :=
        (HistoryProgram.advance_measurable _ _).comp (measurable_const.prodMk measurable_id)
      change ((recodeOracle R dq eo dobs hdq heo hdo).law (eq (A.query s),h)).map
        (fun o => HistoryProgram.advance (BorelAdaptive.channelProgram A eq dobs heq hdo)
          (recodeOracle R dq eo dobs hdq heo hdo) ((s,h),o))=_
      rw [recodeOracle_law,hQ,Measure.map_map hm heo]
      congr 1
      funext o
      simp [HistoryProgram.advance,HistoryProgram.request,BorelAdaptive.channelProgram,
        recodeOracle,hQ,hO]

include hQ hO in
theorem channel_trajectory :
    HistoryProgram.trajectory (BorelAdaptive.channelProgram A eq dobs heq hdo)
      (recodeOracle R dq eo dobs hdq heo hdo)=HistoryProgram.trajectory A R := by
  have hk : HistoryProgram.nextKernel (BorelAdaptive.channelProgram A eq dobs heq hdo)
      (recodeOracle R dq eo dobs hdq heo hdo)=HistoryProgram.nextKernel A R := by
    funext n
    unfold HistoryProgram.nextKernel
    rw [channel_step_kernel A R eq dq eo dobs heq hdq heo hdo hQ hO]
  unfold HistoryProgram.trajectory
  simp only [hk]

include hQ hO in
theorem channel_trajectoryLaw {Private : Type*} [MeasurableSpace Private]
    (privateLaw : Measure Private) (start : Private → S) (h₀ : H) :
    HistoryProgram.trajectoryLaw (BorelAdaptive.channelProgram A eq dobs heq hdo)
      (recodeOracle R dq eo dobs hdq heo hdo) privateLaw start h₀=
      HistoryProgram.trajectoryLaw A R privateLaw start h₀ := by
  unfold HistoryProgram.trajectoryLaw
  rw [channel_trajectory A R eq dq eo dobs heq hdq heo hdo hQ hO]

omit [MeasurableSpace H] in
theorem channel_totalCalls (w : HistoryProgram.Path S H) :
    HistoryProgram.totalCalls (BorelAdaptive.channelProgram A eq dobs heq hdo) w=
      HistoryProgram.totalCalls A w := rfl

omit [MeasurableSpace H] in
theorem channel_stoppedOutput (w : HistoryProgram.Path S H) :
    HistoryProgram.stoppedOutput (BorelAdaptive.channelProgram A eq dobs heq hdo) w=
      HistoryProgram.stoppedOutput A w := rfl

section Packed
open PrimitiveGeometry PrimitiveQuery Stateful
variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : Instance G μ L ρ Δ R₀ σf σg)

def Instance.rawOracle : HistoryProgram.Oracle (G.X × G.Y) (FullResponse G.X G.Y) I.History where
  law := I.oracle.law
  markov := inferInstance
  update := I.oracle.update
  update_measurable := I.oracle.update_measurable

theorem Instance.packed_recodeOracle :
    I.historyOracle=recodeOracle I.rawOracle
      (PrimitiveQuery.unpack (X:=G.X) (Y:=G.Y))
      (packResponse (X:=G.X) (Y:=G.Y))
      (splitResponse (X:=G.X) (Y:=G.Y))
      unpack_measurable packResponse_measurable splitResponse_measurable := rfl

/-- Exact coordinate transport of the entire adaptive execution, retaining
private randomization, oracle history, halting, and all paired correlations. -/
theorem Instance.packed_trajectoryLaw
    {S Private : Type*} [MeasurableSpace S] [MeasurableSpace Private]
    (A : BorelAdaptive.Program S (G.X × G.Y) (FullResponse G.X G.Y) G.X)
    (privateLaw : Measure Private) (start : Private → S) :
    HistoryProgram.trajectoryLaw (BorelAdaptive.channelProgram A
      (fun q => pack q.1 q.2) (PrimitiveQuery.decode (X:=G.X) (Y:=G.Y))
      (packLinear.continuous.measurable) decode_measurable)
      I.historyOracle privateLaw start I.initialHistory=
    HistoryProgram.trajectoryLaw A I.rawOracle privateLaw start I.initialHistory := by
  rw [I.packed_recodeOracle]
  exact channel_trajectoryLaw A I.rawOracle
    (fun q => pack q.1 q.2) PrimitiveQuery.unpack packResponse splitResponse
    packLinear.continuous.measurable unpack_measurable
    packResponse_measurable splitResponse_measurable
    (fun _ => rfl) (fun _ => rfl) privateLaw start I.initialHistory

end Packed

end Bilevel.PolishedHistory
