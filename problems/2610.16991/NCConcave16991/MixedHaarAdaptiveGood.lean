import NCConcave16991.MixedHaarAdaptiveLaw

/-! # Fixed-state almost-everywhere Gaussian guards hold along the actual tape -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.MixedHaar

universe u
variable {S W Z : Type u} [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace Z]

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def tapeGood (next : S → W → S) (G : S → W → Prop) :
    (N : ℕ) → S → RevealTape W Z N → Prop
  | 0, _, _ => True
  | N + 1, s, p => G s p.1 ∧ tapeGood next G N (next s p.1) p.2

theorem tapeGood_joint_measurable {next : S → W → S} {G : S → W → Prop}
    (hn : Measurable (fun p : S × W ↦ next p.1 p.2))
    (hG : Measurable (fun p : S × W ↦ G p.1 p.2)) (N : ℕ) :
    Measurable (fun p : S × RevealTape W Z N ↦ tapeGood next G N p.1 p.2) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      exact (hG.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).and
        (ih.comp ((hn.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
          (measurable_snd.comp measurable_snd)))

theorem tapeGood_ae (τ : Measure W) (ν : Measure Z) [IsProbabilityMeasure τ] [IsProbabilityMeasure ν]
    {next : S → W → S} {G : S → W → Prop}
    (hn : Measurable (fun p : S × W ↦ next p.1 p.2))
    (hG : Measurable (fun p : S × W ↦ G p.1 p.2))
    (hgood : ∀ s, ∀ᵐ w ∂τ, G s w) (N : ℕ) (s : S) :
    ∀ᵐ p ∂revealTapeLaw τ ν N, tapeGood next G N s p := by
  induction N generalizing s with
  | zero => exact Filter.Eventually.of_forall (fun _ ↦ trivial)
  | succ N ih =>
      have h1 := (measurePreserving_fst : MeasurePreserving
        (Prod.fst : W × RevealTape W Z N → W) (τ.prod (revealTapeLaw τ ν N)) τ).quasiMeasurePreserving.ae (hgood s)
      have hm : Measurable (fun p : W × RevealTape W Z N ↦ tapeGood next G N (next s p.1) p.2) :=
        (tapeGood_joint_measurable hn hG N).comp
          ((hn.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
      have h2 := (Measure.ae_prod_iff_ae_ae (μ := τ) (measurableSet_setOfPred.mpr hm)).mpr
        (Filter.Eventually.of_forall (fun w ↦ ih (next s w)))
      filter_upwards [h1,h2] with p hp1 hp2
      exact ⟨hp1,hp2⟩

theorem invariant_of_tapeGood {Q : Type u} {next : S → W → S} {G : S → W → Prop}
    (complete : S → Z → Q) (Inv : S → Prop)
    (hstep : ∀ s w, G s w → Inv s → Inv (next s w))
    (N : ℕ) (s : S) (p : RevealTape W Z N) (hs : Inv s) (hg : tapeGood next G N s p) :
    Inv (simulateCompletion next complete N s p).1 := by
  induction N generalizing s with
  | zero => exact hs
  | succ N ih => exact ih (next s p.1) p.2 (hstep s p.1 hg.1 hs) hg.2

end NCConcave16991.MixedHaar
