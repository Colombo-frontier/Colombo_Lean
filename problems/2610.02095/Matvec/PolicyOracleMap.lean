import Matvec.PolicyComposition

/-! Measurable coordinate changes of oracle inputs and replies preserve the
query horizon. In particular, raw real coordinates and `EuclideanSpace` can
be interchanged without any additional oracle call. -/

namespace Matvec.MeasurableSimulation.Policy
open MeasureTheory

universe u v u' v' w s

variable {Q : Type u} {R : Type v} {Q' : Type u'} {R' : Type v'}
  {O : Type w} {Seed : Type s} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace Q'] [MeasurableSpace R'] [MeasurableSpace O] [MeasurableSpace Seed]
  {T : ℕ}

def mapOracle (alg : Policy Q R O T Seed) (encode : Q → Q') (decode : R' → R)
    (he : Measurable encode) (hd : Measurable decode) : Policy Q' R' O T Seed where
  query j seed h := encode (alg.query j seed (decode ∘ h))
  query_measurable j := he.comp ((alg.query_measurable j).comp
    (measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
      hd.comp ((measurable_pi_apply i).comp measurable_snd))))
  output seed h := alg.output seed (decode ∘ h)
  output_measurable := alg.output_measurable.comp
    (measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
      hd.comp ((measurable_pi_apply i).comp measurable_snd)))

theorem mapOracle_transcript (alg : Policy Q R O T Seed) (encode : Q → Q') (decode : R' → R)
    (he : Measurable encode) (hd : Measurable decode) (oracle : Q' → R') (seed : Seed) (j : ℕ) :
    decode ∘ ((alg.mapOracle encode decode he hd).transcript oracle seed j) =
      alg.transcript (decode ∘ oracle ∘ encode) seed j := by
  induction j with
  | zero => exact Subsingleton.elim _ _
  | succ j ih =>
    rw [transcript, Fin.comp_snoc, transcript, ih]
    exact congrArg (fun h : Fin j → R =>
      Fin.snoc (α := fun _ => R) (alg.transcript (decode ∘ oracle ∘ encode) seed j)
        ((decode ∘ oracle ∘ encode) (alg.query j seed h))) ih

theorem mapOracle_run (alg : Policy Q R O T Seed) (encode : Q → Q') (decode : R' → R)
    (he : Measurable encode) (hd : Measurable decode) (oracle : Q' → R') (seed : Seed) :
    (alg.mapOracle encode decode he hd).run oracle seed =
      alg.run (decode ∘ oracle ∘ encode) seed := by
  exact congrArg (alg.output seed) (alg.mapOracle_transcript encode decode he hd oracle seed T)

end Matvec.MeasurableSimulation.Policy
