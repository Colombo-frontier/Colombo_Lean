import Bilevel.BorelAdaptiveCoupling

/-! Fixed-algorithm private-seed interface on the same hard-instance prior.
The initial algorithm state reads only the private seed, not the hidden
instance or future oracle draws. Outputs are tagged with the instance solely
for evaluating its loss, after the algorithm has returned. -/
noncomputable section
open MeasureTheory
namespace Bilevel.BorelAdaptive

variable {S Q O Y I C Private D : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace I] [MeasurableSpace C]
  [MeasurableSpace Private] [MeasurableSpace D]

def seedInput (initial : Private → S) (p : Sample I Private C) : Sample I S C :=
  (p.1,(initial p.2.1,p.2.2))

theorem seedInput_measurable (initial : Private → S) (hi : Measurable initial) :
    Measurable (seedInput (I := I) (C := C) initial) :=
  measurable_fst.prodMk ((hi.comp (measurable_fst.comp measurable_snd)).prodMk
    (measurable_snd.comp measurable_snd))

def seededTime (A : Program S Q O Y) (response : I → Q → C → O) (initial : Private → S)
    (p : Sample I Private C) : ℕ := stopTime A response (seedInput initial p)

def seededCapped (A : Program S Q O Y) (response : I → Q → C → O) (initial : Private → S)
    (n : ℕ) (p : Sample I Private C) : I × Y := (p.1,cappedOutput A response n (seedInput initial p))

def seededStopped (A : Program S Q O Y) (response : I → Q → C → O) (initial : Private → S)
    (p : Sample I Private C) : I × Y := (p.1,stoppedOutput A response (seedInput initial p))

theorem seededTime_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial) : Measurable (seededTime A response initial) :=
  (stopTime_measurable A response hr).comp (seedInput_measurable initial hi)

theorem seededCapped_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial) (n : ℕ) : Measurable (seededCapped A response initial n) :=
  measurable_fst.prodMk ((cappedOutput_measurable A response hr n).comp (seedInput_measurable initial hi))

theorem seededStopped_measurable (A : Program S Q O Y) (response : I → Q → C → O)
    (hr : Measurable (fun p : I × (Q × C) => response p.1 p.2.1 p.2.2))
    (initial : Private → S) (hi : Measurable initial) : Measurable (seededStopped A response initial) :=
  measurable_fst.prodMk ((stoppedOutput_measurable A response hr).comp (seedInput_measurable initial hi))

theorem seededAgreement_ae (A : Program S Q O Y) (response : I → Q → C → O)
    (initial : Private → S) (μ : Measure (Sample I Private C))
    (hterm : ∀ᵐ p ∂μ,Terminated A response (seedInput initial p)) (n : ℕ) :
    ∀ᵐ p ∂μ,seededTime A response initial p≤n → seededStopped A response initial p=seededCapped A response initial n p := by
  filter_upwards [hterm] with p hp
  intro hn
  exact congrArg (Prod.mk p.1) (cappedOutput_agrees A response (seedInput initial p) hp n hn).symm

def virtualSeedInput (initial : Private → S) (data : I → Private → D)
    (p : Sample I Private C) : Sample I (S × D) C :=
  (p.1,((initial p.2.1,data p.1 p.2.1),p.2.2))

theorem virtualSeedInput_measurable (initial : Private → S) (hi : Measurable initial)
    (data : I → Private → D) (hd : Measurable (fun p : I × Private => data p.1 p.2)) :
    Measurable (virtualSeedInput (C := C) initial data) :=
  measurable_fst.prodMk (((hi.comp (measurable_fst.comp measurable_snd)).prodMk
    (hd.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).prodMk
      (measurable_snd.comp measurable_snd))

def seededVirtual (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (initial : Private → S) (data : I → Private → D) (n : ℕ) (p : Sample I Private C) : I × Y :=
  (p.1,virtualOutput A observe n (virtualSeedInput initial data p))

theorem seededVirtual_measurable (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (ho : Measurable (fun p : I × (Q × (C × D)) => observe p.1 p.2.1 p.2.2.1 p.2.2.2))
    (initial : Private → S) (hi : Measurable initial)
    (data : I → Private → D) (hd : Measurable (fun p : I × Private => data p.1 p.2)) (n : ℕ) :
    Measurable (seededVirtual A observe initial data n) :=
  measurable_fst.prodMk ((virtualOutput_measurable A observe ho n).comp
    (virtualSeedInput_measurable initial hi data hd))

theorem seededBlind_measurable (A : Program S Q O Y) (observe : I → Q → C → D → O × D)
    (ho : Measurable (fun p : I × (Q × (C × D)) => observe p.1 p.2.1 p.2.2.1 p.2.2.2))
    (initial : Private → S) (hi : Measurable initial)
    (data : I → Private → D) (hd : Measurable (fun p : I × Private => data p.1 p.2))
    (Good : I → Q → C → D → Prop)
    (hG : MeasurableSet {p : I × (Q × (C × D)) | Good p.1 p.2.1 p.2.2.1 p.2.2.2}) (n : ℕ) :
    MeasurableSet {p : Sample I Private C | BlindRun A observe Good (virtualSeedInput initial data p) n} :=
  (virtualSeedInput_measurable initial hi data hd) (blindRun_measurable A observe ho Good hG n)

omit [MeasurableSpace I] [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace Private] in
theorem seededCapped_eq_virtual (A : Program S Q O Y)
    (response : I → Q → C → O) (observe : I → Q → C → D → O × D)
    (initial : Private → S) (data : I → Private → D) (Good : I → Q → C → D → Prop)
    (hlocal : ∀ i q c d,Good i q c d → response i q c=(observe i q c d).1)
    (p : Sample I Private C) (n : ℕ) (hgood : BlindRun A observe Good (virtualSeedInput initial data p) n) :
    seededCapped A response initial n p=seededVirtual A observe initial data n p :=
  congrArg (Prod.mk p.1) (cappedOutput_eq_virtual A response observe Good hlocal
    (virtualSeedInput initial data p) n hgood)

end Bilevel.BorelAdaptive
