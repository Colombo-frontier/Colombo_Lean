import Bilevel.RawGenieBorelPolicy
import Bilevel.ChiSourceReleaseCounter

/-! Concrete per-frame disclosure bookkeeping for the source success
counter. Each increase reveals precisely the next column; completed ancestor
frames are charged to their own disclosure budget rather than ignored. -/
noncomputable section
open MeasureTheory
namespace Bilevel.FramePrefixDisclosure
open EuclideanGaussian ProjectionPosterior

def prefixSet (T r : ℕ) : Set (Fin T) := {i | i.val<r}

def name (T r s : ℕ) : Option (Fin T) :=
  if h : r<s ∧ r<T then some ⟨r,h.2⟩ else none

def insertName {T : ℕ} (S : Set (Fin T)) : Option (Fin T) → Set (Fin T)
  | none => S
  | some i => insert i S

theorem prefix_step (T r s : ℕ) (hrs : r≤s) (hs : s≤r+1) (hsT : s≤T) :
    insertName (prefixSet T r) (name T r s)=prefixSet T s := by
  by_cases he : r=s
  · subst s
    simp [name,insertName]
  · have hlt : r<s := by omega
    have hrT : r<T := by omega
    have heq : s=r+1 := by omega
    have hn : name T r s=some ⟨r,hrT⟩ := dif_pos ⟨hlt,hrT⟩
    rw [hn]
    ext i
    simp only [insertName,Set.mem_insert_iff,prefixSet,Set.mem_setOf_eq,Fin.ext_iff]
    omega

theorem name_some_iff (T r s : ℕ) (i : Fin T) :
    name T r s=some i ↔ r<s ∧ i.val=r := by
  unfold name
  split_ifs with h
  · simp only [Option.some.injEq,Fin.ext_iff]
    exact ⟨fun he => ⟨h.1,he.symm⟩,fun he => he.2.symm⟩
  · simp only [reduceCtorEq,false_iff,not_and]
    intro hrs he
    exact h ⟨hrs,he ▸ i.isLt⟩

theorem name_measurable (T : ℕ) [MeasurableSpace (Option (Fin T))] :
    Measurable (fun p : ℕ × ℕ => name T p.1 p.2) :=
  measurable_of_countable _

def prefixSpace {D T : ℕ} (U : Frame D T) (r : ℕ) : Submodule ℝ (Space D) :=
  Submodule.span ℝ (U '' prefixSet T r)

def enlarged {D T : ℕ} (V : Submodule ℝ (Space D)) (U : Frame D T) :
    Option (Fin T) → Submodule ℝ (Space D)
  | none => V
  | some i => V ⊔ Submodule.span ℝ {U i}

theorem prefixSpace_step {D T r s : ℕ} (U : Frame D T) (hrs : r≤s) (hs : s≤r+1) (hsT : s≤T) :
    enlarged (prefixSpace U r) U (name T r s)=prefixSpace U s := by
  have hp := prefix_step T r s hrs hs hsT
  cases hn : name T r s with
  | none =>
    simpa only [hn,insertName] using congrArg (fun S => Submodule.span ℝ (U '' S)) hp
  | some i =>
    simp only [hn,insertName] at hp
    unfold prefixSpace
    rw [←hp]
    have him : U '' insert i (prefixSet T r)=insert (U i) (U '' prefixSet T r) := Set.image_insert_eq
    rw [him,Submodule.span_insert]
    exact sup_comm _ _

theorem prefixSpace_le_enlarged {D T r s : ℕ} (U : Frame D T) (V : Submodule ℝ (Space D))
    (hV : prefixSpace U r≤V) (hrs : r≤s) (hs : s≤r+1) (hsT : s≤T) :
    prefixSpace U s≤enlarged V U (name T r s) := by
  rw [←prefixSpace_step U hrs hs hsT]
  cases name T r s with
  | none => exact hV
  | some i => exact sup_le_sup_right hV _

def count (f : ℕ → ℕ) (q : ℕ) : ℕ := ∑ k∈Finset.range q,if f k<f (k+1) then 1 else 0

theorem count_eq (f : ℕ → ℕ) (h0 : f 0=0) (hstep : ∀ q,f q≤f (q+1) ∧ f (q+1)≤f q+1)
    (q : ℕ) : count f q=f q := by
  induction q with
  | zero => simp [count,h0]
  | succ q ih =>
    rw [count,Finset.sum_range_succ]
    change count f q+(if f q<f (q+1) then 1 else 0)=f (q+1)
    rw [ih]
    have hs := hstep q
    split_ifs <;> omega

theorem nodeBudget_zero (n : ℕ → ℕ) (d j : ℕ) (I : List ℕ) :
    ChiTreeProgress.nodeBudget n d j 0 I=0 := by
  induction I generalizing d j with
  | nil => rfl
  | cons i I ih =>
    simp only [ChiTreeProgress.nodeBudget,ChiTreeProgress.childBudget,Nat.zero_sub,Nat.min_zero]
    exact ih (d-1) (j+1)

theorem inner_zero (n : ℕ → ℕ) (J j : ℕ) (I : List ℕ) :
    ChiTreeProgress.innerCounter n J 0 j I=0 := by
  unfold ChiTreeProgress.innerCounter ChiTreeProgress.counter
  split_ifs
  · rw [nodeBudget_zero]
    cases J+1-(j+1) <;>
      simp [ChiTreeProgress.nodePrefix,ChiTreeProgress.parentPrefix]
  · rfl

theorem inner_le (n : ℕ → ℕ) (J q j : ℕ) (I : List ℕ) :
    ChiTreeProgress.innerCounter n J q j I≤n (j+1)+1 := by
  unfold ChiTreeProgress.innerCounter ChiTreeProgress.counter
  split_ifs
  · exact ChiTreeProgress.nodePrefix_le _ _ _ _
  · omega

def sourceName (n : ℕ → ℕ) (J q j : ℕ) (I : List ℕ) : Option (Fin (n (j+1)+1)) :=
  name (n (j+1)+1) (ChiTreeProgress.innerCounter n J q j I)
    (ChiTreeProgress.innerCounter n J (q+1) j I)

theorem source_prefix_step (n : ℕ → ℕ) (J q j : ℕ) (I : List ℕ) :
    insertName (prefixSet (n (j+1)+1) (ChiTreeProgress.innerCounter n J q j I)) (sourceName n J q j I)=
      prefixSet (n (j+1)+1) (ChiTreeProgress.innerCounter n J (q+1) j I) :=
  prefix_step _ _ _ (ChiTreeProgress.inner_counter_success_bounds n J q j I).1
    (ChiTreeProgress.inner_counter_success_bounds n J q j I).2 (inner_le n J (q+1) j I)

theorem source_revelations_le (n : ℕ → ℕ) (J q j : ℕ) (I : List ℕ) :
    count (fun q => ChiTreeProgress.innerCounter n J q j I) q≤n (j+1)+1 := by
  rw [count_eq (fun q => ChiTreeProgress.innerCounter n J q j I) (inner_zero n J j I)
    (fun q => ChiTreeProgress.inner_counter_success_bounds n J q j I)]
  exact inner_le n J q j I

theorem sourceName_measurable (n : ℕ → ℕ) (J j : ℕ) (I : List ℕ)
    [MeasurableSpace (Option (Fin (n (j+1)+1)))] :
    Measurable (fun q => sourceName n J q j I) := measurable_of_countable _

end Bilevel.FramePrefixDisclosure

