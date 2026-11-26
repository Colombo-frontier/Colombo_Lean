import FreshGradientMinimax.BernoulliCoins
import FreshGradientMinimax.Transcript

/-! Independent Bernoulli words generate exactly the actual adaptive
history kernel. The final output is included and the private seed is retained. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

namespace Algorithm
variable {dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm dx dy Seed)

def coinRun (A : Algorithm dx dy Seed) (q : Bool → Joint dx dy → Joint dx dy) :
    (n : ℕ) → (Fin n → Bool) → Seed → RunState dx dy Seed n
  | 0 => fun _ => initial
  | n + 1 => fun w seed => A.deterministicStep (q (w (Fin.last n))) n
      (A.coinRun q n (fun i => w i.castSucc) seed)

theorem coinRun_snoc (q : Bool → Joint dx dy → Joint dx dy) (n : ℕ)
    (w : Fin n → Bool) (c : Bool) (seed : Seed) :
    A.coinRun q (n + 1) (Fin.snoc w c) seed =
      A.deterministicStep (q c) n (A.coinRun q n w seed) := by
  simp only [coinRun, Fin.snoc_last, Fin.snoc_castSucc]

theorem coinRun_measurable_seed (q : Bool → Joint dx dy → Joint dx dy)
    (hq : ∀ c, Measurable (q c)) (n : ℕ) (w : Fin n → Bool) :
    Measurable (A.coinRun q n w) := by
  induction n with
  | zero => exact initial_measurable
  | succ n ih => exact (A.deterministicStep_measurable (hq _) n).comp (ih _)

theorem coinRun_measurable (q : Bool → Joint dx dy → Joint dx dy)
    (hq : ∀ c, Measurable (q c)) (n : ℕ) :
    Measurable (fun z : Seed × (Fin n → Bool) => A.coinRun q n z.2 z.1) :=
  measurable_from_prod_countable (fun w => A.coinRun_measurable_seed q hq n w)

theorem stepKernel_bernoulli_coin {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (q : Bool → Joint dx dy → Joint dx dy) (hq : ∀ c, Measurable (q c))
    (n : ℕ) (s : RunState dx dy Seed n) :
    A.stepKernel (bernoulliKernel p (q true) (q false) (hq true) (hq false)) n s =
      (coinLaw p).map (fun c => A.deterministicStep (q c) n s) := by
  letI := bernoulliKernel_markov hp hp1 (q true) (q false) (hq true) (hq false)
  rw [stepKernel, Kernel.map_apply _ (A.append_measurable n), Kernel.prod_apply, Kernel.id_apply]
  change ((Measure.dirac s).prod (bernoulliKernel p (q true) (q false) (hq true) (hq false)
    (A.query n s))).map (A.append n) = _
  rw [Measure.dirac_prod, Measure.map_map (A.append_measurable n) measurable_prodMk_left,
    bernoulliKernel_eq_coin_map,
    Measure.map_map ((A.append_measurable n).comp measurable_prodMk_left) (measurable_of_countable _)]
  congr 1
  funext c
  cases c <;> rfl

theorem historyKernel_bernoulli_coin {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (q : Bool → Joint dx dy → Joint dx dy) (hq : ∀ c, Measurable (q c))
    (n : ℕ) (seed : Seed) :
    A.historyKernel (bernoulliKernel p (q true) (q false) (hq true) (hq false)) n seed =
      (coinWordLaw p n).map (fun w => A.coinRun q n w seed) := by
  letI := bernoulliKernel_markov hp hp1 (q true) (q false) (hq true) (hq false)
  induction n with
  | zero =>
    rw [coinWordLaw, Measure.map_dirac (measurable_of_countable _)]
    rfl
  | succ n ih =>
    ext t ht
    rw [historyKernel, Kernel.comp_apply' _ _ _ ht, ih,
      lintegral_map ((A.stepKernel _ n).measurable_coe ht) (measurable_of_countable _),
      coinWordLaw, Measure.map_map (measurable_of_countable _) (coinSnoc_measurable n),
      Measure.map_apply (measurable_of_countable _) ht,
      Measure.prod_apply ((measurable_of_countable _) ht)]
    apply lintegral_congr
    intro w
    rw [A.stepKernel_bernoulli_coin hp hp1 q hq,
      Measure.map_apply (measurable_of_countable _) ht]
    congr 1
    ext c
    simp only [Set.mem_preimage, Function.comp_apply, coinSnoc, A.coinRun_snoc]

theorem outputLaw_bernoulli_coin (ν : Measure Seed) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (q : Bool → Joint dx dy → Joint dx dy) (hq : ∀ c, Measurable (q c)) (n : ℕ) :
    A.outputLaw ν (bernoulliKernel p (q true) (q false) (hq true) (hq false)) n =
      (ν.prod (coinWordLaw p n)).map (fun z => A.output n (A.coinRun q n z.2 z.1)) := by
  letI := bernoulliKernel_markov hp hp1 (q true) (q false) (hq true) (hq false)
  have hf : Measurable (fun z : Seed × (Fin n → Bool) => A.output n (A.coinRun q n z.2 z.1)) :=
    (A.output_measurable n).comp (A.coinRun_measurable q hq n)
  ext t ht
  rw [outputLaw, Measure.bind_apply ht (A.outputKernel _ n).aemeasurable,
    Measure.map_apply hf ht, Measure.prod_apply (hf ht)]
  apply lintegral_congr
  intro seed
  rw [outputKernel, Kernel.map_apply' _ (A.output_measurable n) _ ht,
    A.historyKernel_bernoulli_coin hp hp1 q hq,
    Measure.map_apply (measurable_of_countable _) ((A.output_measurable n) ht)]
  rfl

end Algorithm
end FreshGradientMinimax
