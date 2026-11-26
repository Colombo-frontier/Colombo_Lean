import SecondOrder.UniformFibers
import SecondOrder.RademacherHoeffding

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

abbrev PairIndex (m : ℕ) := Fin m × Bool

/-- A sign vector on 2m coordinates, with exactly m signs of each kind. -/
abbrev BalancedSigns (m : ℕ) :=
  {w : PairIndex m → Bool // ∀ b : Bool, Fintype.card {i // w i = b} = m}

def baseSignFiber (m : ℕ) (b : Bool) : {i : PairIndex m // i.2 = b} ≃ Fin m where
  toFun i := i.1.1
  invFun i := ⟨(i,b), rfl⟩
  left_inv i := by apply Subtype.ext; exact Prod.ext rfl i.property.symm
  right_inv _ := rfl

theorem baseSignFiber_card (m : ℕ) (b : Bool) :
    Fintype.card {i : PairIndex m // i.2 = b} = m := by
  simpa using Fintype.card_congr (baseSignFiber m b)

def balancedBase (m : ℕ) : BalancedSigns m := ⟨Prod.snd, baseSignFiber_card m⟩

instance balancedSigns_nonempty (m : ℕ) : Nonempty (BalancedSigns m) := ⟨balancedBase m⟩

def balancedSignLaw (m : ℕ) : Measure (BalancedSigns m) :=
  (PMF.uniformOfFintype (BalancedSigns m)).toMeasure

instance balancedSignLaw_probability (m : ℕ) : IsProbabilityMeasure (balancedSignLaw m) := by
  unfold balancedSignLaw
  infer_instance

def balancedShuffle {m : ℕ} (π : Equiv.Perm (PairIndex m)) : BalancedSigns m :=
  ⟨fun i => (π i).2, fun b =>
    (Fintype.card_congr (π.subtypeEquivOfSubtype (p := fun j => j.2 = b))).trans (baseSignFiber_card m b)⟩

def balancedRepresentative {m : ℕ} (w : BalancedSigns m) : Equiv.Perm (PairIndex m) :=
  Equiv.ofFiberEquiv (f := w.1) (g := Prod.snd) (fun b =>
    Fintype.equivOfCardEq ((w.property b).trans (baseSignFiber_card m b).symm))

theorem balancedRepresentative_spec {m : ℕ} (w : BalancedSigns m) (i : PairIndex m) :
    (balancedRepresentative w i).2 = w.1 i :=
  Equiv.ofFiberEquiv_map _ i

theorem balancedShuffle_surjective (m : ℕ) :
    Function.Surjective (@balancedShuffle m) := by
  intro w
  refine ⟨balancedRepresentative w, ?_⟩
  apply Subtype.ext
  funext i
  exact balancedRepresentative_spec w i

def balancedShuffleFiber {m : ℕ} (w : BalancedSigns m) :
    {π : Equiv.Perm (PairIndex m) // balancedShuffle π = w} ≃
      {π : Equiv.Perm (PairIndex m) // balancedShuffle π = balancedBase m} :=
  (Equiv.mulRight (balancedRepresentative w).symm).subtypeEquiv (fun π => by
    constructor
    · intro h
      apply Subtype.ext
      funext i
      have hh := congrFun (congrArg Subtype.val h) ((balancedRepresentative w).symm i)
      change (π ((balancedRepresentative w).symm i)).2 = i.2
      rw [show (π ((balancedRepresentative w).symm i)).2 =
        w.1 ((balancedRepresentative w).symm i) from hh,
        ← balancedRepresentative_spec, Equiv.apply_symm_apply]
    · intro h
      apply Subtype.ext
      funext i
      have hh := congrFun (congrArg Subtype.val h) (balancedRepresentative w i)
      change (π i).2 = w.1 i
      simpa only [Equiv.coe_mulRight, balancedShuffle, Equiv.Perm.mul_apply,
        Equiv.symm_apply_apply, balancedBase, balancedRepresentative_spec] using hh)

/-- Uniformly permuting the paired base vector gives precisely the
uniform distribution on all balanced vectors. -/
theorem balancedShuffle_uniformMean {m : ℕ} (X : BalancedSigns m → ℝ) :
    uniformMean (fun π : Equiv.Perm (PairIndex m) => X (balancedShuffle π)) = uniformMean X :=
  uniformMean_of_fiber_equiv balancedShuffle (balancedBase m) (balancedShuffle_surjective m)
    balancedShuffleFiber X

def balancedSignSum {m : ℕ} (a : PairIndex m → ℝ) (w : BalancedSigns m) : ℝ :=
  ∑ i, a i*signValue (w.1 i)

theorem balancedSignLaw_real_indicator {m : ℕ} (S : Set (BalancedSigns m)) :
    (balancedSignLaw m).real S = uniformMean (fun w => if w ∈ S then (1:ℝ) else 0) :=
  uniformMeasure_real_indicator S

def pairOrientation {m : ℕ} (ε : Fin m → Bool) : Equiv.Perm (PairIndex m) where
  toFun i := (i.1, if ε i.1 then i.2 else !i.2)
  invFun i := (i.1, if ε i.1 then i.2 else !i.2)
  left_inv i := by rcases i with ⟨i,b⟩; cases he : ε i <;> cases b <;> simp [he]
  right_inv i := by rcases i with ⟨i,b⟩; cases he : ε i <;> cases b <;> simp [he]

theorem pairOrientation_sign {m : ℕ} (ε : Fin m → Bool) (i : Fin m) (b : Bool) :
    signValue ((pairOrientation ε (i,b)).2) = signValue (ε i)*signValue b := by
  cases he : ε i <;> cases b <;> norm_num [pairOrientation, signValue, he]

def pairDifference {m : ℕ} (a : PairIndex m → ℝ) (π : Equiv.Perm (PairIndex m)) (i : Fin m) : ℝ :=
  a (π.symm (i,true))-a (π.symm (i,false))

theorem balancedSignSum_oriented {m : ℕ} (a : PairIndex m → ℝ)
    (π : Equiv.Perm (PairIndex m)) (ε : Fin m → Bool) :
    balancedSignSum a (balancedShuffle (pairOrientation ε*π)) = rademacherSum (pairDifference a π) ε := by
  have he := Equiv.sum_comp π (fun j : PairIndex m => a (π.symm j)*
    signValue ((pairOrientation ε j).2))
  simp only [Equiv.symm_apply_apply] at he
  change (∑ i, a i*signValue ((pairOrientation ε (π i)).2)) = _
  rw [he, Fintype.sum_prod_type]
  unfold rademacherSum pairDifference
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  simp only [pairOrientation_sign]
  cases he : ε i <;> norm_num [signValue, he] <;> ring

/-- Adding independent fair orientations leaves the uniform balanced
law unchanged. Conditional on the permutation, the sum is a Rademacher sum. -/
theorem balancedSignSum_mixture {m : ℕ} (a : PairIndex m → ℝ) (X : ℝ → ℝ) :
    uniformMean (fun w : BalancedSigns m => X (balancedSignSum a w)) =
      uniformMean (fun π : Equiv.Perm (PairIndex m) =>
        uniformMean (fun ε : Fin m → Bool => X (rademacherSum (pairDifference a π) ε))) := by
  simp_rw [← balancedSignSum_oriented]
  rw [uniformMean_comm]
  have he (ε : Fin m → Bool) := uniformMean_equiv (Equiv.mulLeft (pairOrientation ε))
    (fun π => X (balancedSignSum a (balancedShuffle π)))
  simp only [Equiv.coe_mulLeft] at he
  simp only [he, uniformMean_const]
  exact (balancedShuffle_uniformMean (fun w => X (balancedSignSum a w))).symm

end
end SecondOrder
