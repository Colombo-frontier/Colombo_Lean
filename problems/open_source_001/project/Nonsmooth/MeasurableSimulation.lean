import Nonsmooth.OracleSimulation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {Ω S X Z : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [MeasurableSpace X] [MeasurableSpace Z]

structure Policy.IsMeasurable (p : Policy Ω S X) : Prop where
  initial : Measurable p.initial
  query : ∀ n, Measurable (fun z : Ω × S => p.query n z.1 z.2)
  update : ∀ n, Measurable (fun z : Ω × S × ℝ => p.update n z.1 z.2.1 z.2.2)
  output : Measurable (fun z : Ω × S => p.output z.1 z.2)

theorem simulation_measurable {p : Policy Ω S X} (hp : p.IsMeasurable)
    {q : X → Z} (hq : Measurable q) {reconstruct : X → ℝ → ℝ}
    (hr : Measurable (fun z : X × ℝ => reconstruct z.1 z.2)) :
    (p.simulate q reconstruct).IsMeasurable := by
  refine ⟨hp.initial, fun n => hq.comp (hp.query n), ?_, hq.comp hp.output⟩
  intro n
  have hs : Measurable (fun z : Ω × S × ℝ => z.2.1) := measurable_fst.comp measurable_snd
  have hy : Measurable (fun z : Ω × S × ℝ => z.2.2) := measurable_snd.comp measurable_snd
  have hquery : Measurable (fun z : Ω × S × ℝ => p.query n z.1 z.2.1) :=
    (hp.query n).comp (measurable_fst.prodMk hs)
  have hresponse := hr.comp (hquery.prodMk hy)
  exact (hp.update n).comp (measurable_fst.prodMk (hs.prodMk hresponse))

theorem policy_run_measurable {p : Policy Ω S X} (hp : p.IsMeasurable)
    {f : X → ℝ} (hf : Measurable f) (T : ℕ) : Measurable (fun ω => p.run f ω T) := by
  induction T with
  | zero => exact hp.initial
  | succ n ih =>
    have hq : Measurable (fun ω => p.query n ω (p.run f ω n)) :=
      (hp.query n).comp (measurable_id.prodMk ih)
    exact (hp.update n).comp (measurable_id.prodMk (ih.prodMk (hf.comp hq)))

theorem policy_output_measurable {p : Policy Ω S X} (hp : p.IsMeasurable)
    {f : X → ℝ} (hf : Measurable f) (T : ℕ) : Measurable (fun ω => p.result f ω T) :=
  hp.output.comp (measurable_id.prodMk (policy_run_measurable hp hf T))

/-- Pointwise loss transfer can be integrated over the same seed law, with no exchange of adversary
and seed quantifiers. Integrability is an explicit hypothesis, not a hidden axiom. -/
theorem simulation_expected_loss {p : Policy Ω S X} (q : X → Z)
    (reconstruct : X → ℝ → ℝ) (f : Z → ℝ) (F : X → ℝ)
    (hexact : ∀ x, reconstruct x (f (q x)) = F x)
    (P : Measure Ω) (T : ℕ) (fstar Fstar A : ℝ)
    (hpoint : ∀ x, A * (f (q x) - fstar) ≤ F x - Fstar)
    (hi : Integrable (fun ω => f ((p.simulate q reconstruct).result f ω T) - fstar) P)
    (hI : Integrable (fun ω => F (p.result F ω T) - Fstar) P) :
    A * (∫ ω, f ((p.simulate q reconstruct).result f ω T) - fstar ∂P) ≤
      ∫ ω, F (p.result F ω T) - Fstar ∂P := by
  rw [← integral_const_mul]
  apply integral_mono (hi.const_mul A) hI
  intro ω
  change A * (f ((p.simulate q reconstruct).result f ω T) - fstar) ≤
    F (p.result F ω T) - Fstar
  rw [simulation_output_exact p q reconstruct f F hexact ω T]
  exact hpoint _

end
end Nonsmooth
