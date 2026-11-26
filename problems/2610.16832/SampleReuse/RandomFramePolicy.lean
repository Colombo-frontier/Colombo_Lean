import SampleReuse.RandomFramePrefix
import SampleReuse.RandomFrameSequential

noncomputable section
namespace SampleReuse.RandomFrame

variable {Ω E X Y : Type*}

/-- The first `N` stages are actual ideal queries; the last stage is the
algorithm's output based on the entire ideal response history. -/
def policyStages (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y) (N : ℕ)
    (output : Ω → (Fin N → Y) → X) :
    ∀ r : Fin (N+1), Ω × (Fin r.val → E) → X :=
  Fin.lastCases
    (fun p => output p.1 (prefixHistory query reply p.1 N p.2))
    (fun r => prefixQuery query reply r.val)

@[simp] theorem policyStages_query (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y) (N : ℕ)
    (output : Ω → (Fin N → Y) → X) (r : Fin N) :
    policyStages query reply N output r.castSucc = prefixQuery query reply r.val := by
  simp only [policyStages, Fin.lastCases_castSucc]

@[simp] theorem policyStages_output (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y) (N : ℕ)
    (output : Ω → (Fin N → Y) → X) :
    policyStages query reply N output (Fin.last N) =
      fun p => output p.1 (prefixHistory query reply p.1 N p.2) := by
  simp only [policyStages, Fin.lastCases_last]

variable [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace X] [MeasurableSpace Y]

theorem measurable_policyStages (query : ∀ n, Ω → (Fin n → Y) → X)
    (reply : ∀ n, (Fin (n+1) → E) → X → Y)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → Y) => query n p.1 p.2))
    (hr : ∀ n, Measurable (fun p : (Fin (n+1) → E) × X => reply n p.1 p.2))
    (N : ℕ) (output : Ω → (Fin N → Y) → X)
    (hout : Measurable (fun p : Ω × (Fin N → Y) => output p.1 p.2))
    (r : Fin (N+1)) : Measurable (policyStages query reply N output r) := by
  induction r using Fin.lastCases with
  | last =>
      rw [policyStages_output]
      exact measurable_prefixOutput query reply hq hr N output hout
  | cast r =>
      rw [policyStages_query]
      exact measurable_prefixQuery query reply hq hr r.val

end SampleReuse.RandomFrame
