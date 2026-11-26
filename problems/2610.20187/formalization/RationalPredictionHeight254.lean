import RationalTaylorHeight254
import RationalSparseLearner254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem RationalHeight.neg {x : ℚ} {b : ℕ} (h : RationalHeight x b) : RationalHeight (-x) b :=
  MatrixHeight.neg h

theorem RationalHeight.sub {x y : ℚ} {b c : ℕ}
    (hx : RationalHeight x b) (hy : RationalHeight y c) : RationalHeight (x-y) (b+c+1) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem rationalSparsePrediction_height {d n : ℕ} (S : RationalSparseData d n)
    (live : Finset (Fin n)) (b c : ℕ) (hsupport : ∀ e,e∉live → S.weights e=0)
    (hw : ∀ e∈live,RationalHeight (S.weights e) b)
    (hm : ∀ e∈live,∀ j,RationalHeight ((S.histories e).mean j) c) (j : Fin d) :
    RationalHeight (rationalSparsePrediction S j) (live.card*(b+c+2)) := by
  have heq : rationalSparsePrediction S j=∑ e∈live,S.weights e*(S.histories e).mean j := by
    unfold rationalSparsePrediction
    exact (Finset.sum_subset (Finset.subset_univ live) (by
      intro e _ he
      simp [hsupport e he])).symm
  rw [heq]
  exact RationalHeight.sum live _ (b+c+1) (fun e he=>(hw e he).mul (hm e he j))

theorem rationalSparsePrediction_bits {d n : ℕ} (S : RationalSparseData d n)
    (live : Finset (Fin n)) (b c : ℕ) (hsupport : ∀ e,e∉live → S.weights e=0)
    (hw : ∀ e∈live,RationalHeight (S.weights e) b)
    (hm : ∀ e∈live,∀ j,RationalHeight ((S.histories e).mean j) c) (j : Fin d) :
    (rationalSparsePrediction S j).num.natAbs.size≤live.card*(b+c+2)+1 ∧
    (rationalSparsePrediction S j).den.size≤live.card*(b+c+2)+1 :=
  (rationalSparsePrediction_height S live b c hsupport hw hm j).reduced_bits

theorem rationalExponent_height {d : ℕ} (g w x : Fin d→ℚ) (lam : ℚ)
    (bg bw bx bl : ℕ) (hg : ∀ j,RationalHeight (g j) bg)
    (hw : ∀ j,RationalHeight (w j) bw) (hx : ∀ j,RationalHeight (x j) bx)
    (hlam : RationalHeight lam bl) :
    RationalHeight (-lam*rationalCoordinateSurrogate lam g w x)
      (3*(d*(bg+bx+bw+3))+2*bl+5) := by
  let Z := d*(bg+bx+bw+3)
  have hz : RationalHeight (g ⬝ᵥ (x-w)) Z := by
    have hh := RationalHeight.sum Finset.univ (fun j=>g j*(x j-w j)) (bg+(bx+bw+1)+1)
      (fun j _=>(hg j).mul ((hx j).sub (hw j)))
    simpa only [Z,Finset.card_univ,Fintype.card_fin,dotProduct,Pi.sub_apply,Nat.add_assoc,Nat.reduceAdd] using hh
  have hh := hlam.neg.mul (hz.add (hlam.mul (hz.pow 2)))
  change RationalHeight (-lam*(g ⬝ᵥ (x-w)+lam*(g ⬝ᵥ (x-w))^2)) _ at hh
  change RationalHeight (-lam*(g ⬝ᵥ (x-w)+lam*(g ⬝ᵥ (x-w))^2)) _
  convert hh using 1 <;> dsimp [Z] <;> ring

end Paper254
#print axioms Paper254.rationalSparsePrediction_bits
#print axioms Paper254.rationalExponent_height
