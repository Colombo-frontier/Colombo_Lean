import SampleReuse.Model
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

/-! A concrete count of words with at most half as many distinct labels as
positions. This is the combinatorial input to a trace-even-moment argument;
this file does not assert a matrix concentration theorem. -/

open scoped BigOperators

namespace SampleReuse
noncomputable section
open Classical

abbrev SmallWord (n k : ℕ) :=
  {w : Fin (2*k) → Fin n // (Finset.univ.image w).card ≤ k}

abbrev WordCode (n k : ℕ) :=
  Σ F : {s : Finset (Fin (2*k)) // s.card ≤ k},
    (F.1 → Fin n) × (↥(F.1ᶜ) → F.1)

def decodeWord {n k : ℕ} (c : WordCode n k) : Fin (2*k) → Fin n :=
  fun i => if hi : i ∈ c.1.1 then c.2.1 ⟨i, hi⟩
    else c.2.1 (c.2.2 ⟨i, Finset.mem_compl.mpr hi⟩)

theorem word_representatives {n k : ℕ} (w : SmallWord n k) :
    ∃ F : Finset (Fin (2*k)), F.card ≤ k ∧
      ∀ i, ∃ j ∈ F, w.1 j = w.1 i := by
  let labels := Finset.univ.image w.1
  have hex (b : labels) : ∃ i : Fin (2*k), w.1 i = b.1 := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp b.2
    exact ⟨i, hi⟩
  let r : labels → Fin (2*k) := fun b => Classical.choose (hex b)
  have hr (b : labels) : w.1 (r b) = b.1 := Classical.choose_spec (hex b)
  have hinj : Function.Injective r := by
    intro a b hab
    apply Subtype.ext
    rw [← hr a, ← hr b, hab]
  refine ⟨Finset.univ.image r, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_coe]
    exact w.2
  · intro i
    let b : labels := ⟨w.1 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    exact ⟨r b, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩, hr b⟩

def wordRepresentativeSet {n k : ℕ} (w : SmallWord n k) : Finset (Fin (2*k)) :=
  Classical.choose (word_representatives w)

theorem wordRepresentativeSet_spec {n k : ℕ} (w : SmallWord n k) :
    (wordRepresentativeSet w).card ≤ k ∧
      ∀ i, ∃ j ∈ wordRepresentativeSet w, w.1 j = w.1 i :=
  Classical.choose_spec (word_representatives w)

theorem wordPointer_exists {n k : ℕ} (w : SmallWord n k) (i : Fin (2*k)) :
    ∃ j : wordRepresentativeSet w, w.1 j = w.1 i := by
  obtain ⟨j, hj, heq⟩ := (wordRepresentativeSet_spec w).2 i
  exact ⟨⟨j, hj⟩, heq⟩

def wordPointer {n k : ℕ} (w : SmallWord n k) (i : Fin (2*k)) :
    wordRepresentativeSet w := Classical.choose (wordPointer_exists w i)

theorem wordPointer_spec {n k : ℕ} (w : SmallWord n k) (i : Fin (2*k)) :
    w.1 (wordPointer w i) = w.1 i := Classical.choose_spec (wordPointer_exists w i)

def encodeWord {n k : ℕ} (w : SmallWord n k) : WordCode n k :=
  ⟨⟨wordRepresentativeSet w, (wordRepresentativeSet_spec w).1⟩,
    (fun j => w.1 j), (fun i => wordPointer w i)⟩

theorem decode_encodeWord {n k : ℕ} (w : SmallWord n k) :
    decodeWord (encodeWord w) = w.1 := by
  funext i
  unfold encodeWord decodeWord
  dsimp only
  split_ifs with hi
  · rfl
  · exact wordPointer_spec w i

theorem encodeWord_injective {n k : ℕ} :
    Function.Injective (@encodeWord n k) := by
  intro u v h
  apply Subtype.ext
  have hd := congrArg decodeWord h
  simpa only [decode_encodeWord] using hd

theorem wordCode_fiber_card (n k : ℕ)
    (F : {s : Finset (Fin (2*k)) // s.card ≤ k}) :
    Fintype.card ((F.1 → Fin n) × (↥(F.1ᶜ) → F.1)) =
      n ^ F.1.card * F.1.card ^ (2*k-F.1.card) := by
  simp [Fintype.card_fun, Finset.card_compl]

theorem wordCode_fiber_bound {n k j : ℕ} (hj : j ≤ k) (hn : k ≤ n) :
    n ^ j * j ^ (2*k-j) ≤ n ^ k * k ^ k := by
  have he : 2*k-j = (k-j)+k := by omega
  calc
    _ ≤ n^j * k^(2*k-j) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hj _)
    _ = (n^j * k^(k-j)) * k^k := by rw [he, pow_add, mul_assoc]
    _ ≤ (n^j * n^(k-j)) * k^k :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _))
    _ = n^k * k^k := by rw [← pow_add, Nat.add_sub_of_le hj]

/-- The actual cardinality of all length-`2*k` words using at most `k`
distinct labels, with no combinatorial premise left to the caller. -/
theorem smallWord_card_le {n k : ℕ} (hn : k ≤ n) :
    Fintype.card (SmallWord n k) ≤ (4*k*n)^k := by
  have hsets : Fintype.card {s : Finset (Fin (2*k)) // s.card ≤ k} ≤ 2^(2*k) := by
    calc
      _ ≤ Fintype.card (Finset (Fin (2*k))) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = _ := by simp
  calc
    _ ≤ Fintype.card (WordCode n k) :=
      Fintype.card_le_of_injective encodeWord encodeWord_injective
    _ = ∑ F : {s : Finset (Fin (2*k)) // s.card ≤ k},
        n^F.1.card * F.1.card^(2*k-F.1.card) := by
      simp only [WordCode, Fintype.card_sigma, wordCode_fiber_card]
    _ ≤ ∑ _F : {s : Finset (Fin (2*k)) // s.card ≤ k}, n^k*k^k := by
      apply Finset.sum_le_sum
      intro F _
      exact wordCode_fiber_bound F.2 hn
    _ = Fintype.card {s : Finset (Fin (2*k)) // s.card ≤ k} * (n^k*k^k) := by
      simp
    _ ≤ 2^(2*k) * (n^k*k^k) := Nat.mul_le_mul_right _ hsets
    _ = (4*k*n)^k := by
      rw [pow_mul]
      norm_num
      rw [mul_pow, mul_pow]
      ring

def NoSingletonWord {n k : ℕ} (w : Fin (2*k) → Fin n) : Prop :=
  ∀ i, ∃ j, j ≠ i ∧ w j = w i

theorem noSingletonWord_support_le {n k : ℕ} {w : Fin (2*k) → Fin n}
    (hw : NoSingletonWord w) : (Finset.univ.image w).card ≤ k := by
  have htwo : ∀ b ∈ Finset.univ.image w,
      2 ≤ (Finset.univ.filter (fun i => w i = b)).card := by
    intro b hb
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
    obtain ⟨j, hji, hj⟩ := hw i
    have hs : {i, j} ⊆ Finset.univ.filter (fun a => w a = b) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · simp [hi]
      · simp [hj, hi]
    calc
      2 = ({i, j} : Finset _).card := (Finset.card_pair hji.symm).symm
      _ ≤ _ := Finset.card_le_card hs
  have hsum := Finset.sum_le_sum htwo
  have hc := Finset.card_eq_sum_card_image w (Finset.univ : Finset (Fin (2*k)))
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have he : ∑ b ∈ Finset.univ.image w,
      (Finset.univ.filter (fun i => w i = b)).card = 2*k := hc.symm
  rw [he] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  omega

/-- The non-singleton words in a centered independent matrix moment expansion
are counted by `(4*k*n)^k` when the sample count is at least the moment order. -/
theorem noSingletonWord_card_le {n k : ℕ} (hn : k ≤ n) :
    Fintype.card {w : Fin (2*k) → Fin n // NoSingletonWord w} ≤ (4*k*n)^k := by
  let f : {w : Fin (2*k) → Fin n // NoSingletonWord w} → SmallWord n k :=
    fun w => ⟨w.1, noSingletonWord_support_le w.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : SmallWord n k => z.1) hab
  exact (Fintype.card_le_of_injective f hf).trans (smallWord_card_le hn)

end
end SampleReuse
