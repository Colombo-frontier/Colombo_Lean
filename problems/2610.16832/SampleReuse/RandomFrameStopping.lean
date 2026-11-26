import SampleReuse.RandomFrameCalibrated
import SampleReuse.RandomFrameExpectedBudget

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory
open scoped Classical

variable {Ω X Y Θ : Type*}

/-- Scan a finite full history and preserve the output at its first stop. If
the execution has not stopped, return the output at the imposed cap. -/
def stopScan (stop : ∀ n, Ω → (Fin n → Y) → Bool)
    (output : ∀ n, Ω → (Fin n → Y) → X) (ω : Ω) : (n : ℕ) → (Fin n → Y) → Bool × X
  | 0, z => (stop 0 ω z, output 0 ω z)
  | n+1, z =>
      let old := stopScan stop output ω n (fun i => z i.castSucc)
      if old.1 = true then old else (stop (n+1) ω z, output (n+1) ω z)

theorem measurable_stopScan [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (stop : ∀ n, Ω → (Fin n → Y) → Bool) (output : ∀ n, Ω → (Fin n → Y) → X)
    (hs : ∀ n, Measurable (fun p : Ω × (Fin n → Y) => stop n p.1 p.2))
    (ho : ∀ n, Measurable (fun p : Ω × (Fin n → Y) => output n p.1 p.2)) (n : ℕ) :
    Measurable (fun p : Ω × (Fin n → Y) => stopScan stop output p.1 n p.2) := by
  induction n with
  | zero => exact (hs 0).prodMk (ho 0)
  | succ n ih =>
      have hp : Measurable (fun p : Ω × (Fin (n+1) → Y) =>
          stopScan stop output p.1 n (fun i => p.2 i.castSucc)) :=
        ih.comp (measurable_fst.prodMk (measurable_pi_lambda _
          (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)))
      exact Measurable.ite (hp.fst (measurableSet_singleton true)) hp
        ((hs (n+1)).prodMk (ho (n+1)))

def runScan (query : ∀ n, Ω → (Fin n → Y) → X) (oracle : ℕ → Θ → X → Y)
    (stop : ∀ n, Ω → (Fin n → Y) → Bool) (output : ∀ n, Ω → (Fin n → Y) → X)
    (ω : Ω) (θ : Θ) (n : ℕ) : Bool × X :=
  stopScan stop output ω n (responseHistory query oracle ω θ n)

theorem runScan_succ (query : ∀ n, Ω → (Fin n → Y) → X) (oracle : ℕ → Θ → X → Y)
    (stop : ∀ n, Ω → (Fin n → Y) → Bool) (output : ∀ n, Ω → (Fin n → Y) → X)
    (ω : Ω) (θ : Θ) (n : ℕ) :
    runScan query oracle stop output ω θ (n+1) =
      if (runScan query oracle stop output ω θ n).1 = true then
        runScan query oracle stop output ω θ n else
        (stop (n+1) ω (responseHistory query oracle ω θ (n+1)),
          output (n+1) ω (responseHistory query oracle ω θ (n+1))) := by
  simp only [runScan, stopScan, responseHistory, Fin.snoc_castSucc]

theorem runScan_no_stop (query : ∀ n, Ω → (Fin n → Y) → X) (oracle : ℕ → Θ → X → Y)
    (stop : ∀ n, Ω → (Fin n → Y) → Bool) (output : ∀ n, Ω → (Fin n → Y) → X)
    (ω : Ω) (θ : Θ) (n : ℕ)
    (hs : ∀ k ≤ n, stop k ω (responseHistory query oracle ω θ k) = false) :
    runScan query oracle stop output ω θ n =
      (false, output n ω (responseHistory query oracle ω θ n)) := by
  induction n with
  | zero => exact Prod.ext (hs 0 le_rfl) rfl
  | succ n ih =>
      rw [runScan_succ, ih (fun k hk => hs k (by omega))]
      simp only [Bool.false_eq_true, ↓reduceIte, hs (n+1) le_rfl]

theorem runScan_first_stop (query : ∀ n, Ω → (Fin n → Y) → X) (oracle : ℕ → Θ → X → Y)
    (stop : ∀ n, Ω → (Fin n → Y) → Bool) (output : ∀ n, Ω → (Fin n → Y) → X)
    (ω : Ω) (θ : Θ) (c n : ℕ) (hcn : c ≤ n)
    (hc : stop c ω (responseHistory query oracle ω θ c) = true)
    (hs : ∀ k < c, stop k ω (responseHistory query oracle ω θ k) = false) :
    runScan query oracle stop output ω θ n =
      (true, output c ω (responseHistory query oracle ω θ c)) := by
  induction n with
  | zero =>
      have he : c = 0 := by omega
      subst c
      exact Prod.ext hc rfl
  | succ n ih =>
      by_cases hn : c ≤ n
      · rw [runScan_succ, ih hn]
        simp only [↓reduceIte]
      · have he : c = n+1 := by omega
        subst c
        rw [runScan_succ, runScan_no_stop query oracle stop output ω θ n
          (fun k hk => hs k (by omega))]
        simp only [Bool.false_eq_true, ↓reduceIte, hc]

structure StoppingFullJetPolicy (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d
  query_measurable : ∀ n, Measurable
    (fun p : Ω × (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) => query n p.1 p.2)
  stop : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Bool
  stop_measurable : ∀ n, Measurable
    (fun p : Ω × (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) => stop n p.1 p.2)
  output : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d
  output_measurable : ∀ n, Measurable
    (fun p : Ω × (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) => output n p.1 p.2)

namespace StoppingFullJetPolicy

variable {d : ℕ} [MeasurableSpace Ω]

def cap (π : StoppingFullJetPolicy d Ω) (N : ℕ) : FullJetPolicy d N Ω where
  query := π.query
  query_measurable := π.query_measurable
  output := fun ω z => (stopScan π.stop π.output ω N z).2
  output_measurable := (measurable_stopScan π.stop π.output π.stop_measurable π.output_measurable N).snd

def Halts (π : StoppingFullJetPolicy d Ω) (f : Point d → ℝ) (ω : Ω) : Prop :=
  ∃ n, π.stop n ω (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () n) = true

def cost (π : StoppingFullJetPolicy d Ω) (f : Point d → ℝ) (ω : Ω) : ℕ :=
  if hh : π.Halts f ω then Nat.find hh else 0

def outputFor (π : StoppingFullJetPolicy d Ω) (f : Point d → ℝ) (ω : Ω) : Point d :=
  π.output (π.cost f ω) ω
    (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () (π.cost f ω))

theorem cap_agrees (π : StoppingFullJetPolicy d Ω) (f : Point d → ℝ) (ω : Ω)
    (hh : π.Halts f ω) (N : ℕ) (hN : π.cost f ω ≤ N) :
    (π.cap N).outputFor f ω = π.outputFor f ω := by
  have hcost : π.cost f ω = Nat.find hh := dif_pos hh
  have hn : Nat.find hh ≤ N := by simpa only [hcost] using hN
  have hs := runScan_first_stop π.query (fun _ (_ : Unit) => fullJet f) π.stop π.output
    ω () (Nat.find hh) N hn (Nat.find_spec hh) (fun k hk => by
      cases h : π.stop k ω (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () k)
      · rfl
      · exact False.elim (Nat.find_min hh hk h))
  change (stopScan π.stop π.output ω N
    (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () N)).2 =
      π.output (π.cost f ω) ω
        (responseHistory π.query (fun _ (_ : Unit) => fullJet f) ω () (π.cost f ω))
  rw [hcost]
  exact congrArg Prod.snd hs

end StoppingFullJetPolicy
end SampleReuse.RandomFrame
