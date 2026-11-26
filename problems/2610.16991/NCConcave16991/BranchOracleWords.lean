import NCConcave16991.BranchAccounting
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Monotone.Basic

/-! # Concrete deletion-closed reachable words and simultaneous updates -/

namespace NCConcave16991.BranchOracle
noncomputable section
open scoped BigOperators

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]

abbrev Word (t : ℕ) := Fin t → ι

structure WordProfile where
  words : ∀ t, Finset (Word ι t)
  deletion : ∀ t w, w ∈ words (t + 1) → Fin.tail w ∈ words t

namespace WordProfile

variable {ι}

theorem head_tail_injective (t : ℕ) : Function.Injective (fun w : Word ι (t + 1) ↦ (w 0, Fin.tail w)) := by
  intro w v h
  have hh := congrArg (fun p : ι × Word ι t ↦ Fin.cons (α := fun _ : Fin (t + 1) ↦ ι) p.1 p.2) h
  simpa only [Fin.cons_self_tail] using hh

theorem card_step (p : WordProfile ι) (t : ℕ) :
    (p.words (t + 1)).card ≤ Fintype.card ι * (p.words t).card := by
  let S := (p.words (t + 1)).image (fun w ↦ (w 0, Fin.tail w))
  have hS : S.card = (p.words (t + 1)).card := Finset.card_image_of_injective _ (head_tail_injective t)
  rw [← hS]
  apply BranchAccounting.deletion_closed_card_bound S (p.words t)
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  exact p.deletion t v hv

def mass (p : WordProfile ι) (t : ℕ) : ℝ := (p.words t).card / (Fintype.card ι : ℝ) ^ t

theorem mass_nonneg (p : WordProfile ι) (t : ℕ) : 0 ≤ p.mass t := by unfold mass; positivity

theorem mass_le_one (p : WordProfile ι) (t : ℕ) : p.mass t ≤ 1 := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hh : ((p.words t).card : ℝ) ≤ (Fintype.card ι : ℝ) ^ t := by
    have hc := Finset.card_le_univ (p.words t)
    have hw : Fintype.card (Word ι t) = Fintype.card ι ^ t := by simp [Word, Fintype.card_fun]
    rw [hw] at hc
    exact_mod_cast hc
  exact (div_le_one (pow_pos hn _)).mpr hh

theorem mass_step (p : WordProfile ι) (t : ℕ) : p.mass (t + 1) ≤ p.mass t := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc : ((p.words (t + 1)).card : ℝ) ≤ (Fintype.card ι : ℝ) * (p.words t).card := by
    exact_mod_cast p.card_step t
  unfold mass
  apply (div_le_div_iff₀ (pow_pos hn _) (pow_pos hn _)).mpr
  rw [pow_succ]
  have hh := mul_le_mul_of_nonneg_right hc (pow_nonneg hn.le t)
  nlinarith only [hh]

def massProfile (p : WordProfile ι) : BranchAccounting.MassProfile where
  mass := p.mass
  nonneg := p.mass_nonneg
  le_one := p.mass_le_one
  antitone := antitone_nat_of_succ_le p.mass_step

def root : WordProfile ι where
  words t := if t = 0 then Finset.univ else ∅
  deletion := by intro t w hw; simp at hw

def stepWords (p : WordProfile ι) (i : ι) : ∀ t, Finset (Word ι t)
  | 0 => p.words 0
  | t + 1 => p.words (t + 1) ∪ (p.words t).image (Fin.cons i)

theorem words_subset_stepWords (p : WordProfile ι) (i : ι) (t : ℕ) : p.words t ⊆ p.stepWords i t := by
  cases t with
  | zero => exact Finset.Subset.refl _
  | succ t => exact Finset.subset_union_left

def matrixStep (p : WordProfile ι) (i : ι) : WordProfile ι where
  words := p.stepWords i
  deletion := by
    intro t w hw
    rcases Finset.mem_union.mp hw with ho | hn
    · exact p.words_subset_stepWords i t (p.deletion t w ho)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
      rw [Fin.tail_cons]
      exact p.words_subset_stepWords i t hv

theorem matrixStep_card (p : WordProfile ι) (i : ι) (t : ℕ) :
    ((p.matrixStep i).words (t + 1)).card ≤ (p.words (t + 1)).card + (p.words t).card := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)

theorem matrixStep_mass_zero (p : WordProfile ι) (i : ι) : (p.matrixStep i).mass 0 = p.mass 0 := rfl

theorem matrixStep_mass_step (p : WordProfile ι) (i : ι) (t : ℕ) :
    (p.matrixStep i).mass (t + 1) ≤ p.mass (t + 1) + p.mass t / (Fintype.card ι : ℝ) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc : (((p.matrixStep i).words (t + 1)).card : ℝ) ≤
      (p.words (t + 1)).card + (p.words t).card := by exact_mod_cast p.matrixStep_card i t
  have hh := div_le_div_of_nonneg_right hc (pow_nonneg hn.le (t + 1))
  unfold mass
  calc
    _ ≤ ((p.words (t + 1)).card + (p.words t).card : ℝ) / (Fintype.card ι : ℝ) ^ (t + 1) := hh
    _ = _ := by rw [pow_succ]; field_simp [hn.ne'] <;> ring

end WordProfile
end
end NCConcave16991.BranchOracle
