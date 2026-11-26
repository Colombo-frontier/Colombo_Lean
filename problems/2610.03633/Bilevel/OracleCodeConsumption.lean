import Bilevel.OracleCode

/-! The stream evaluator consumes exactly its reported number of original
calls. In particular a zero-call branch consumes no oracle randomness. -/
noncomputable section
namespace Bilevel.OracleCode
variable {Q O A B : Space} {Seed : Type*}

theorem eval_suffix (response : Q → Seed → O) (c : Code Q O A B)
    (a : A) (s : IndependentStream.Stream Seed) :
    (eval response c (a,s)).2=fun n => s ((eval response c (a,s)).1.2.2+n) := by
  induction c generalizing s with
  | pure f hf => simp [eval]
  | call => funext n; simp [eval,IndependentStream.tail,Nat.add_comm]
  | bind p q hp hq =>
      dsimp only [eval]
      rw [hq]
      funext n
      rw [hp]
      simp only [Stateful.Procedure.combine,Nat.add_assoc]
  | reparam p f hf hp => exact hp (f a) s
  | choose p n hn hp => exact hp (n a) a s

end Bilevel.OracleCode
