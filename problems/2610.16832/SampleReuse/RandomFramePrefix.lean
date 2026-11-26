import SampleReuse.RandomFrameTranscript

/-! Explicit dependence of an ideal execution on only the revealed columns.
Each ideal response is computed from its available prefix, and complete history
policies remain unrestricted measurable functions of all previous replies. -/

noncomputable section
namespace SampleReuse.RandomFrame

variable {Ω Θ E X Y : Type*}

def prefixHistory (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y) (ω : Ω) :
    (n : ℕ) → (Fin n → E) → (Fin n → Y)
  | 0, _ => Fin.elim0
  | n+1, z =>
      let old := prefixHistory query reply ω n (fun i => z i.castSucc)
      Fin.snoc old (reply n z (query n ω old))

def prefixQuery (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y) (n : ℕ) (p : Ω × (Fin n → E)) : X :=
  query n p.1 (prefixHistory query reply p.1 n p.2)

def prefixOracle (reply : ∀ n, (Fin (n+1) → E) → X → Y)
    (columns : Θ → ℕ → E) (n : ℕ) (θ : Θ) : X → Y :=
  reply n (fun i => columns θ i.val)

/-- The ideal transcript is a function of the actual prefix alone. -/
theorem responseHistory_eq_prefixHistory (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y) (columns : Θ → ℕ → E)
    (ω : Ω) (θ : Θ) (n : ℕ) :
    responseHistory query (prefixOracle reply columns) ω θ n =
      prefixHistory query reply ω n (fun i => columns θ i.val) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [responseHistory, prefixHistory, ih, prefixOracle]; rfl

theorem queryAt_eq_prefixQuery (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y) (columns : Θ → ℕ → E)
    (ω : Ω) (θ : Θ) (n : ℕ) :
    queryAt query (prefixOracle reply columns) ω θ n =
      prefixQuery query reply n (ω, fun i => columns θ i.val) := by
  simp only [queryAt, prefixQuery, responseHistory_eq_prefixHistory]

variable [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace X] [MeasurableSpace Y]

theorem measurable_prefixHistory (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → Y) => query n p.1 p.2))
    (hr : ∀ n, Measurable (fun p : (Fin (n+1) → E) × X => reply n p.1 p.2)) (n : ℕ) :
    Measurable (fun p : Ω × (Fin n → E) => prefixHistory query reply p.1 n p.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hold : Measurable (fun p : Ω × (Fin (n+1) → E) =>
          prefixHistory query reply p.1 n (fun i => p.2 i.castSucc)) :=
        ih.comp (measurable_fst.prodMk (measurable_pi_lambda _
          (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)))
      apply measurable_pi_lambda
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [prefixHistory, Fin.snoc_last] using
          (hr n).comp (measurable_snd.prodMk ((hq n).comp (measurable_fst.prodMk hold)))
      · simpa only [prefixHistory, Fin.snoc_castSucc] using
          (measurable_pi_apply j).comp hold

theorem measurable_prefixQuery (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → Y) => query n p.1 p.2))
    (hr : ∀ n, Measurable (fun p : (Fin (n+1) → E) × X => reply n p.1 p.2)) (n : ℕ) :
    Measurable (prefixQuery query reply n) :=
  (hq n).comp (measurable_fst.prodMk (measurable_prefixHistory query reply hq hr n))

theorem measurable_prefixOutput (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → Y) => query n p.1 p.2))
    (hr : ∀ n, Measurable (fun p : (Fin (n+1) → E) × X => reply n p.1 p.2))
    (N : ℕ) (output : Ω → (Fin N → Y) → X)
    (hout : Measurable (fun p : Ω × (Fin N → Y) => output p.1 p.2)) :
    Measurable (fun p : Ω × (Fin N → E) => output p.1 (prefixHistory query reply p.1 N p.2)) :=
  hout.comp (measurable_fst.prodMk (measurable_prefixHistory query reply hq hr N))

end SampleReuse.RandomFrame
