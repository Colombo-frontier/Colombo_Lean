import SampleReuse.PersistentHandleFirstOrder
import SampleReuse.PersistentSuccessProbability

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section

/-- The final point query is an uncharged output slot. Its handle is never
evaluated; all earlier requests and replies are exactly the original ones. -/
def persistentOutputPolicy {Q H Y S : Type*}
    (P : OracleAlgorithm (Q × H) Y Q S) (N : ℕ) : QueryPolicy (Q × H) Y S where
  initial := P.initial
  query n s := if n = N then (P.output n s,(P.query n s).2) else P.query n s
  update := P.update

theorem persistentOutputPolicy_run {Q H Y S Z : Type*}
    (P : OracleAlgorithm (Q × H) Y Q S) (reply : Q → Z → Y) (table : H → Z) (N : ℕ) :
    ∀ n, n ≤ N → persistentQueryRun (persistentOutputPolicy P N) reply table n =
      persistentQueryRun P.toQueryPolicy reply table n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hne : n ≠ N := by omega
    simp only [persistentQueryRun]
    rw [ih (by omega)]
    simp only [persistentOutputPolicy,if_neg hne]

theorem persistentOutputPolicy_firstOrder {d T : ℕ} {H S : Type}
    (P : OracleAlgorithm (Point (FirstOrderDimension d T) × H)
      (RichReply (FirstOrderDimension d T)) (Point (FirstOrderDimension d T)) S)
    (Θ : Fin (T+1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : H → FirstOrderCoefficients d T R) (N : ℕ) :
    persistentOriginalOutput (persistentOutputPolicy P N) Θ A β table N =
      P.output N (persistentQueryRun P.toQueryPolicy
        (fun x z => richReply (scaledFirstOrderSample Θ A β) z x) table N) := by
  unfold persistentOriginalOutput
  rw [← persistentQueryRun_firstOrder,persistentOutputPolicy_run P _ table N N le_rfl]
  simp [persistentOutputPolicy]

end
end SampleReuse
