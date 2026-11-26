import SampleReuse.RandomFrameLaw
import SecondOrder.ScalarJetEquality

/-! Full response histories, arbitrary measurable policies, and exact coupling.
The call count may be zero; the output is an arbitrary function of the coins and
complete response history, with no span or norm restriction. -/

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory

variable {Ω Θ X Y : Type*}

def responseHistory (query : ∀ n, Ω → (Fin n → Y) → X)
    (oracle : ℕ → Θ → X → Y) (ω : Ω) (θ : Θ) : (n : ℕ) → (Fin n → Y)
  | 0 => Fin.elim0
  | n + 1 => Fin.snoc (responseHistory query oracle ω θ n)
      (oracle n θ (query n ω (responseHistory query oracle ω θ n)))

def queryAt (query : ∀ n, Ω → (Fin n → Y) → X)
    (oracle : ℕ → Θ → X → Y) (ω : Ω) (θ : Θ) (n : ℕ) : X :=
  query n ω (responseHistory query oracle ω θ n)

theorem measurable_responseHistory [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace X] [MeasurableSpace Y]
    (query : ∀ n, Ω → (Fin n → Y) → X) (oracle : ℕ → Θ → X → Y)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → Y) => query n p.1 p.2))
    (ho : ∀ n, Measurable (fun p : Θ × X => oracle n p.1 p.2)) (n : ℕ) :
    Measurable (fun p : Ω × Θ => responseHistory query oracle p.1 p.2 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      apply measurable_pi_lambda
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [responseHistory, Fin.snoc_last] using
          (ho n).comp (measurable_snd.prodMk ((hq n).comp (measurable_fst.prodMk ih)))
      · simpa only [responseHistory, Fin.snoc_castSucc] using
          (measurable_pi_apply j).comp ih

theorem measurable_queryAt [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MeasurableSpace X] [MeasurableSpace Y]
    (query : ∀ n, Ω → (Fin n → Y) → X) (oracle : ℕ → Θ → X → Y)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → Y) => query n p.1 p.2))
    (ho : ∀ n, Measurable (fun p : Θ × X => oracle n p.1 p.2)) (n : ℕ) :
    Measurable (fun p : Ω × Θ => queryAt query oracle p.1 p.2 n) :=
  (hq n).comp (measurable_fst.prodMk (measurable_responseHistory query oracle hq ho n))

/-- Equality of the actual oracle responses along the ideal execution implies
equality of complete transcripts. No equality at unqueried points is required. -/
theorem responseHistory_coupling (query : ∀ n, Ω → (Fin n → Y) → X)
    (realOracle idealOracle : ℕ → Θ → X → Y) (ω : Ω) (θ : Θ) (N : ℕ)
    (hreply : ∀ n < N, realOracle n θ (queryAt query idealOracle ω θ n) =
      idealOracle n θ (queryAt query idealOracle ω θ n)) :
    responseHistory query realOracle ω θ N = responseHistory query idealOracle ω θ N := by
  have hprefix (n : ℕ) (hn : n ≤ N) :
      responseHistory query realOracle ω θ n = responseHistory query idealOracle ω θ n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        have hp := ih (by omega)
        simp only [responseHistory, hp]
        rw [show realOracle n θ (query n ω (responseHistory query idealOracle ω θ n)) =
          idealOracle n θ (query n ω (responseHistory query idealOracle ω θ n)) from
          hreply n (by omega)]
  exact hprefix N le_rfl

theorem output_coupling (query : ∀ n, Ω → (Fin n → Y) → X)
    (realOracle idealOracle : ℕ → Θ → X → Y) (ω : Ω) (θ : Θ) (N : ℕ)
    (output : Ω → (Fin N → Y) → X)
    (hreply : ∀ n < N, realOracle n θ (queryAt query idealOracle ω θ n) =
      idealOracle n θ (queryAt query idealOracle ω θ n)) :
    output ω (responseHistory query realOracle ω θ N) =
      output ω (responseHistory query idealOracle ω θ N) := by
  rw [responseHistory_coupling query realOracle idealOracle ω θ N hreply]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def fullJet (f : E → ℝ) (x : E) : ℝ × E × (E →L[ℝ] E) :=
  (f x, gradient f x, fderiv ℝ (gradient f) x)

theorem fullJet_eq_of_scalarJetEq {f g : E → ℝ} {x : E}
    (h : SecondOrder.ScalarJetEq f g x) : fullJet f x = fullJet g x :=
  Prod.ext h.value (Prod.ext h.gradient_eq h.hessian_eq)

theorem fullJet_transcript_coupling
    (query : ∀ n, Ω → (Fin n → ℝ × E × (E →L[ℝ] E)) → E)
    (f : Θ → E → ℝ) (g : ℕ → Θ → E → ℝ) (ω : Ω) (θ : Θ) (N : ℕ)
    (hjet : ∀ n < N, SecondOrder.ScalarJetEq (f θ) (g n θ)
      (queryAt query (fun n θ => fullJet (g n θ)) ω θ n)) :
    responseHistory query (fun _ θ => fullJet (f θ)) ω θ N =
      responseHistory query (fun n θ => fullJet (g n θ)) ω θ N := by
  apply responseHistory_coupling
  intro n hn
  exact fullJet_eq_of_scalarJetEq (hjet n hn)

end SampleReuse.RandomFrame
