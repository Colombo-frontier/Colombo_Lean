import Bilevel.PolishedHistorySourceCompiled
import Bilevel.PolishedHistoryModel

/-! The repaired source experiment supplies the exact history-dependent full
SFO interface consumed by the cached algorithm proof. Full L2 vector moments
are converted to the original x/y blocks without changing the response law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory
open PrimitiveGeometry PrimitiveQuery Stateful
set_option autoImplicit false
variable (G : Geometry)

def rawReadUpper (o : FullResponse G.X G.Y) : G.Query := pack o.1.1 o.1.2

def rawReadLower (o : FullResponse G.X G.Y) : G.Query := pack o.2.1 o.2.2

theorem rawReadUpper_measurable : Measurable (rawReadUpper G) :=
  packLinear.continuous.measurable.comp measurable_fst

theorem rawReadLower_measurable : Measurable (rawReadLower G) :=
  packLinear.continuous.measurable.comp measurable_snd

variable {Q S B : Type*} [MeasurableSpace Q] [MeasurableSpace S] [MeasurableSpace B]
  {A : BorelAdaptive.Program S Q (FullResponse G.X G.Y) B}
  {tf tg : Q → G.Query} {σf σg : ℝ}
  (E : SourceExperiment A tf tg (rawReadUpper G) (rawReadLower G) σf σg)
  (htf : Measurable tf) (htg : Measurable tg)

def exactRawResponse (q : Q) : FullResponse G.X G.Y :=
  (PrimitiveQuery.unpack (tf q),PrimitiveQuery.unpack (tg q))

include htf htg in
theorem exactRawResponse_measurable : Measurable (exactRawResponse G (tf:=tf) (tg:=tg)) :=
  (unpack_measurable.comp htf).prodMk (unpack_measurable.comp htg)

def SourceExperiment.fullSFO : HistorySFO (Query:=Q) (History:=S × ℕ) (X:=G.X) (Y:=G.Y) σf σg := by
  let R := E.repairedOracle htf htg (rawReadUpper_measurable G) (rawReadLower_measurable G)
    (exactRawResponse G) (exactRawResponse_measurable G htf htg)
  have good (q : Q) (h : S × ℕ) := E.repairedOracle_good
    htf htg (rawReadUpper_measurable G) (rawReadLower_measurable G)
    (exactRawResponse G) (exactRawResponse_measurable G htf htg)
    (fun _ => rfl) (fun _ => rfl) q h
  exact {
    law := R.law
    markov := inferInstance
    update := R.update
    update_measurable := R.update_measurable
    upper := FullGradientLaw.ofFullVector R.law (rawReadUpper G) tf
      (rawReadUpper_measurable G) htf σf (fun q h => (good q h).1)
    lower := FullGradientLaw.ofFullVector R.law (rawReadLower G) tg
      (rawReadLower_measurable G) htg σg (fun q h => (good q h).2) }

theorem SourceExperiment.fullSFO_law :
    (E.fullSFO G htf htg).law=(E.repairedOracle htf htg
      (rawReadUpper_measurable G) (rawReadLower_measurable G)
      (exactRawResponse G) (exactRawResponse_measurable G htf htg)).law := rfl

theorem SourceExperiment.fullSFO_update :
    (E.fullSFO G htf htg).update=(E.repairedOracle htf htg
      (rawReadUpper_measurable G) (rawReadLower_measurable G)
      (exactRawResponse G) (exactRawResponse_measurable G htf htg)).update := rfl

theorem SourceExperiment.fullSFO_upper_truth (q : Q) :
    (E.fullSFO G htf htg).upper.truth_x q=(tf q).1 ∧
      (E.fullSFO G htf htg).upper.truth_y q=(tf q).2 := ⟨rfl,rfl⟩

theorem SourceExperiment.fullSFO_lower_truth (q : Q) :
    (E.fullSFO G htf htg).lower.truth_x q=(tg q).1 ∧
      (E.fullSFO G htf htg).lower.truth_y q=(tg q).2 := ⟨rfl,rfl⟩

end Bilevel.PolishedHistory
