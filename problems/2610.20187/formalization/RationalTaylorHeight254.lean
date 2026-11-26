import RationalMatrixHeight254
import RationalExp254

noncomputable section
open Matrix
open scoped BigOperators
namespace Paper254

def RationalHeight (x : ℚ) (b : ℕ) : Prop := MatrixHeight (fun _ _ : Fin 1=>x) b

theorem RationalHeight.mono {x : ℚ} {b c : ℕ} (h : RationalHeight x b) (hbc : b≤c) :
    RationalHeight x c := MatrixHeight.mono h hbc

theorem RationalHeight.of_int (z : ℤ) (b : ℕ) (hz : |z|≤(2:ℤ)^b) : RationalHeight (z:ℚ) b :=
  ⟨fun _ _=>z,1,by norm_num,one_le_pow₀ (by norm_num),fun _ _=>hz,by intros; simp⟩

theorem RationalHeight.zero : RationalHeight 0 0 := by
  simpa using RationalHeight.of_int 0 0 (by norm_num)

theorem RationalHeight.one : RationalHeight 1 0 := by
  simpa using RationalHeight.of_int 1 0 (by norm_num)

theorem RationalHeight.add {x y : ℚ} {b c : ℕ} (hx : RationalHeight x b) (hy : RationalHeight y c) :
    RationalHeight (x+y) (b+c+1) := MatrixHeight.add hx hy

theorem RationalHeight.mul {x y : ℚ} {b c : ℕ} (hx : RationalHeight x b) (hy : RationalHeight y c) :
    RationalHeight (x*y) (b+c+1) := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hx
  obtain ⟨W,r,hr0,hrb,hW,hs⟩ := hy
  have hp : (2:ℤ)^b*2^c≤2^(b+c+1) := by
    rw [←pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨fun _ _=>Z 0 0*W 0 0,q*r,mul_ne_zero hq hr0,?_,?_,?_⟩
  · rw [abs_mul]
    exact (mul_le_mul hqb hrb (abs_nonneg _) (by positivity)).trans hp
  · intro i j
    rw [abs_mul]
    exact (mul_le_mul (hZ 0 0) (hW 0 0) (abs_nonneg _) (by positivity)).trans hp
  · intro i j
    change x*y=_
    dsimp only at hr hs
    rw [hr 0 0,hs 0 0]
    push_cast
    exact div_mul_div_comm _ _ _ _

theorem RationalHeight.inv {x : ℚ} {b : ℕ} (hx : RationalHeight x b) : RationalHeight x⁻¹ b := by
  by_cases h0 : x=0
  · subst x
    simpa using RationalHeight.zero.mono (Nat.zero_le b)
  · exact MatrixHeight.pivot_inverse hx h0

theorem RationalHeight.pow {x : ℚ} {b : ℕ} (hx : RationalHeight x b) (k : ℕ) :
    RationalHeight (x^k) (k*(b+1)) := by
  induction k with
  | zero => simpa using RationalHeight.one
  | succ k ih =>
    have hh := ih.mul hx
    rw [pow_succ]
    convert hh using 1 <;> ring

theorem RationalHeight.sum {ι : Type*} (S : Finset ι) (f : ι→ℚ) (b : ℕ)
    (hf : ∀ i∈S,RationalHeight (f i) b) :
    RationalHeight (∑ i∈S,f i) (S.card*(b+1)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using RationalHeight.zero
  | @insert i S hi ih =>
    have hh := (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))
    rw [Finset.sum_insert hi,Finset.card_insert_of_notMem hi]
    convert hh using 1 <;> ring

theorem RationalHeight.reduced_bits {x : ℚ} {b : ℕ} (h : RationalHeight x b) :
    x.num.natAbs.size≤b+1 ∧ x.den.size≤b+1 := MatrixHeight.reduced_bits h 0 0

theorem rational_factorial_height (k : ℕ) : RationalHeight (k.factorial:ℚ) (k*k) := by
  have hn : k.factorial≤2^(k*k) := by
    calc
      _ ≤ k^k := Nat.factorial_le_pow k
      _ ≤ (2^k)^k := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) k
      _ = _ := by rw [←pow_mul]
  have hi : |(k.factorial:ℤ)|≤(2:ℤ)^(k*k) := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hn
  simpa using RationalHeight.of_int (k.factorial:ℤ) (k*k) hi

/-- Every partial sum is covered, including the actual accumulation order. -/
theorem rationalTaylor_partial_height (x : ℚ) (b n : ℕ) (hx : RationalHeight x b)
    (S : Finset ℕ) (hS : S⊆Finset.range n) :
    RationalHeight (∑ k∈S,x^k/(k.factorial:ℚ)) (n*(n*(b+1)+n*n+2)) := by
  have hterms : ∀ k∈S,RationalHeight (x^k/(k.factorial:ℚ)) (n*(b+1)+n*n+1) := by
    intro k hk
    have hkn : k≤n := by have hh := Finset.mem_range.mp (hS hk); omega
    have hh := (hx.pow k).mul (rational_factorial_height k).inv
    rw [←div_eq_mul_inv] at hh
    apply hh.mono
    have h1 := Nat.mul_le_mul_right (b+1) hkn
    have h2 := Nat.mul_le_mul hkn hkn
    omega
  have hh := RationalHeight.sum S (fun k=>x^k/(k.factorial:ℚ)) _ hterms
  apply hh.mono
  have hc : S.card≤n := by simpa using Finset.card_le_card hS
  exact Nat.mul_le_mul_right _ hc

theorem rationalExp_reduced_bits (x : ℚ) (b p : ℕ) (hx : RationalHeight x b) :
    (rationalExp x p).num.natAbs.size≤(p+3)*((p+3)*(b+1)+(p+3)*(p+3)+2)+1 ∧
    (rationalExp x p).den.size≤(p+3)*((p+3)*(b+1)+(p+3)*(p+3)+2)+1 :=
  (rationalTaylor_partial_height x b (p+3) hx (Finset.range (p+3)) (Finset.Subset.refl _)).reduced_bits

end Paper254
#print axioms Paper254.rationalExp_reduced_bits
