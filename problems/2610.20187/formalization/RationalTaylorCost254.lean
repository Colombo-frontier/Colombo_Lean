import RationalTaylorHeight254

open scoped BigOperators
namespace Paper254

/-- A shared term recurrence: one multiplication, division, and addition
per Taylor coefficient. The term and accumulator are both cached scalars. -/
def countedTaylorState (x : ℚ) : ℕ→ℚ×ℚ×ℕ
  | 0=>(1,0,0)
  | n+1=>
    let S := countedTaylorState x n
    (S.1*x/(n+1),S.2.1+S.1,S.2.2+3)

theorem countedTaylorState_spec (x : ℚ) (n : ℕ) :
    countedTaylorState x n=(x^n/(n.factorial:ℚ),
      ∑ k∈Finset.range n,x^k/(k.factorial:ℚ),3*n) := by
  induction n with
  | zero => simp [countedTaylorState]
  | succ n ih =>
    rw [countedTaylorState,ih,Finset.sum_range_succ]
    simp only [Prod.mk.injEq]
    refine ⟨?_,by trivial,by omega⟩
    rw [pow_succ,Nat.factorial_succ]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

def countedRationalExp (x : ℚ) (p : ℕ) : ℚ×ℕ :=
  let S := countedTaylorState x (p+3)
  (S.2.1,S.2.2)

theorem countedRationalExp_value (x : ℚ) (p : ℕ) :
    (countedRationalExp x p).1=rationalExp x p := by
  simp [countedRationalExp,countedTaylorState_spec,rationalExp]

theorem countedRationalExp_cost (x : ℚ) (p : ℕ) :
    (countedRationalExp x p).2=3*(p+3) := by
  simp [countedRationalExp,countedTaylorState_spec]

theorem countedTaylorState_height (x : ℚ) (b n : ℕ) (hx : RationalHeight x b) :
    RationalHeight (countedTaylorState x n).1 (n*(b+1)+n*n+1) ∧
    RationalHeight (countedTaylorState x n).2.1 (n*(n*(b+1)+n*n+2)) := by
  rw [countedTaylorState_spec]
  refine ⟨?_,rationalTaylor_partial_height x b n hx (Finset.range n) (Finset.Subset.refl _)⟩
  simpa only [div_eq_mul_inv] using (hx.pow n).mul (rational_factorial_height n).inv

theorem countedRationalExp_certificate (x : ℚ) (b p : ℕ) (hx : RationalHeight x b) :
    (countedRationalExp x p).1=rationalExp x p ∧
    (countedRationalExp x p).2=3*(p+3) ∧
    ((countedRationalExp x p).1).num.natAbs.size≤(p+3)*((p+3)*(b+1)+(p+3)*(p+3)+2)+1 ∧
    ((countedRationalExp x p).1).den.size≤(p+3)*((p+3)*(b+1)+(p+3)*(p+3)+2)+1 := by
  refine ⟨countedRationalExp_value x p,countedRationalExp_cost x p,?_⟩
  rw [countedRationalExp_value]
  exact rationalExp_reduced_bits x b p hx

end Paper254
#print axioms Paper254.countedRationalExp_certificate
#eval (Paper254.countedRationalExp (1/4) 6).2
