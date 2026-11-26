import FullyScheduledTransition254

namespace Paper254

/-- Word capacity for clocks, dyadic candidates, numbered keys and live
list indices. Ghost instruction counters are not runtime data. -/
def metadataWordBits (T K : ℕ) : ℕ := Nat.log 2 (T+1)+Nat.log 2 (K+1)+6

theorem metadataWordBound_lt_pow (T K : ℕ) : metadataWordBound T K<2^metadataWordBits T K := by
  have hT := (Nat.lt_pow_succ_log_self (by decide : 1<(2:ℕ)) (T+1)).le
  have hK := (Nat.lt_pow_succ_log_self (by decide : 1<(2:ℕ)) (K+1)).le
  calc
    metadataWordBound T K≤8*2^(Nat.log 2 (T+1)+1)*2^(Nat.log 2 (K+1)+1) := by
      unfold metadataWordBound
      gcongr
    _=2^(Nat.log 2 (T+1)+Nat.log 2 (K+1)+5) := by simp only [pow_add]; norm_num; ring
    _<2^metadataWordBits T K := by
      unfold metadataWordBits
      have he : (2:ℕ)^(Nat.log 2 (T+1)+Nat.log 2 (K+1)+6)=
          2^(Nat.log 2 (T+1)+Nat.log 2 (K+1)+5)*2 := by
        conv_lhs => rw [show Nat.log 2 (T+1)+Nat.log 2 (K+1)+6=
          (Nat.log 2 (T+1)+Nat.log 2 (K+1)+5)+1 by omega]
        exact pow_succ _ _
      rw [he]
      have hp : 0<2^(Nat.log 2 (T+1)+Nat.log 2 (K+1)+5) := by positivity
      omega

theorem metadata_size_le (T K x : ℕ) (hx : x≤metadataWordBound T K) :
    x.size≤metadataWordBits T K := Nat.size_le.mpr (hx.trans_lt (metadataWordBound_lt_pow T K))

theorem metadataWordBound_basic (T K : ℕ) :
    T+2≤metadataWordBound T K ∧ K+1≤metadataWordBound T K ∧ 8≤metadataWordBound T K := by
  unfold metadataWordBound
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem metadata_depth_bound (T t : ℕ) (ht : t≤T+1) : Nat.log 2 t+1≤T+1 := by
  by_cases hz : t=0
  · subst t; simp
  · have hh := Nat.log_lt_self 2 hz; omega

theorem metadata_power_bound (T t k : ℕ) (ht : t≤T+1) (hk : k<Nat.log 2 t+1) :
    2^k≤T+1 := by
  by_cases hz : t=0
  · subst t
    have h0 : k=0 := by simpa using hk
    subst k
    simp
  · exact (Nat.pow_le_of_le_log hz (by omega : k≤Nat.log 2 t)).trans ht

/-- Operands and results of each repeated-division logarithm call.
The recursive argument n/2 remains within the same n bound. -/
def metadataLogWords (n : ℕ) := [n,2,n/2,Nat.log 2 n,Nat.log 2 n+1,0,1]

theorem metadata_log_words (T K n : ℕ) (hn : n≤T+1) :
    ∀ x∈metadataLogWords n,x.size≤metadataWordBits T K := by
  have hb := metadataWordBound_basic T K
  have hd := Nat.div_le_self n 2
  have hl := metadata_depth_bound T n hn
  intro x hx
  apply metadata_size_le
  simp only [metadataLogWords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

/-- The power routine multiplies a prefix power by two at each recursive
return. Every prefix and result fits the same capacity. -/
theorem metadata_power_prefix_words (T K t k j : ℕ) (ht : t≤T+1)
    (hk : k<Nat.log 2 t+1) (hj : j≤k) :
    j.size≤metadataWordBits T K ∧ (2^j).size≤metadataWordBits T K ∧
      (j<k → (2*2^j).size≤metadataWordBits T K) := by
  have hp := metadata_power_bound T t k ht hk
  have hm := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hj
  have hb := metadataWordBound_basic T K
  have hd := metadata_depth_bound T t ht
  refine ⟨metadata_size_le T K j (by omega),metadata_size_le T K (2^j) (by omega),?_⟩
  intro hj'
  have hm' := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show j+1≤k by omega)
  rw [pow_succ,Nat.mul_comm] at hm'
  exact metadata_size_le T K (2*2^j) (by omega)

def metadataCandidateWords (t k q : ℕ) :=
  [t,k,q,2,2^k,2^k*q,t%2^k,2^k*q+t%2^k,t-(2^k*q+t%2^k),Nat.log 2 t+1,5]

theorem metadata_candidate_words (T K t k q : ℕ) (ht : t≤T+1)
    (hk : k<Nat.log 2 t+1) (hq : q<5) :
    ∀ x∈metadataCandidateWords t k q,x.size≤metadataWordBits T K := by
  have hb := metadataWordBound_basic T K
  have hc := metadata_candidate_operands T K t k q ht hk hq
  have hm := Nat.mod_le t (2^k)
  have hs := Nat.sub_le t (2^k*q+t%2^k)
  have hd := metadata_depth_bound T t ht
  intro x hx
  apply metadata_size_le
  simp only [metadataCandidateWords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def metadataActiveWords (t i k : ℕ) := [t,i,k,2,2^k,i%2^k,t-i,4,4*2^k,0,1]

theorem metadata_active_words (T K t i k : ℕ) (ht : t≤T+1) (hi : i≤t)
    (hk : k<Nat.log 2 t+1) :
    ∀ x∈metadataActiveWords t i k,x.size≤metadataWordBits T K := by
  have hb := metadataWordBound_basic T K
  have hc := metadata_candidate_operands T K t k 0 ht hk (by decide)
  have hm := Nat.mod_le i (2^k)
  have hs := Nat.sub_le t i
  have hd := metadata_depth_bound T t ht
  intro x hx
  apply metadata_size_le
  simp only [metadataActiveWords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem countedCandidateList_entries_le (t i : ℕ) (hi : i∈(countedCandidateList t).1) : i≤t := by
  simp only [countedCandidateList,mapWithCosts_values,List.mem_map,countedNatPowTwo_spec] at hi
  obtain ⟨kq,_hkq,rfl⟩ := hi
  exact Nat.sub_le _ _

/-- This discharges the active-test premise for every input actually
produced by the candidate program, including rejected candidates. -/
theorem actual_active_operand_bits (T K t i k : ℕ) (ht : t≤T+1)
    (hi : i∈(countedCandidateList t).1) (hk : k∈List.range (Nat.log 2 t+1)) :
    ∀ x∈metadataActiveWords t i k,x.size≤metadataWordBits T K :=
  metadata_active_words T K t i k ht (countedCandidateList_entries_le t i hi) (List.mem_range.mp hk)

theorem actual_candidate_operand_bits (T K t : ℕ) (ht : t≤T+1) (kq : ℕ×ℕ)
    (hkq : kq∈(List.range (Nat.log 2 t+1)).product (List.range 5)) :
    ∀ x∈metadataCandidateWords t kq.1 kq.2,x.size≤metadataWordBits T K :=
  metadata_candidate_words T K t kq.1 kq.2 ht
    (List.mem_range.mp (List.mem_product.mp hkq).1) (List.mem_range.mp (List.mem_product.mp hkq).2)

theorem countedUniqueSort_mem_iff {α : Type} [LinearOrder α] (xs : List α) (a : α) :
    a∈(countedUniqueSort xs).1 ↔ a∈xs := by
  rw [countedUniqueSort_value]
  simp

theorem actual_short_sort_operand_bits (T K t : ℕ) (ht : t≤T+1) (i : ℕ)
    (hi : i∈(countedFilter (countedActiveTest t) (countedCandidateList t).1).1) :
    i.size≤metadataWordBits T K := by
  rw [countedFilter_value] at hi
  have hh := countedCandidateList_entries_le t i (List.mem_filter.mp hi).1
  exact metadata_size_le T K i (hh.trans (ht.trans (by have hb:=metadataWordBound_basic T K; omega)))

def metadataEncodeWords (K i j : ℕ) := [i,0,1,i-1,K,K+1,j,(i-1)*(K+1),(i-1)*(K+1)+j]

theorem metadata_encode_words (T K i : ℕ) (hi : i≤T+1) (j : Fin (K+1)) :
    ∀ x∈metadataEncodeWords K i j.val,x.size≤metadataWordBits T K := by
  have hb := metadataWordBound_basic T K
  have hj := j.isLt
  have hi' : i-1≤T := by omega
  have hprod : (i-1)*(K+1)≤T*(K+1) := Nat.mul_le_mul_right _ hi'
  have hkey : (i-1)*(K+1)+j.val<(T+1)*(K+1) := by nlinarith
  have hM : (T+1)*(K+1)≤metadataWordBound T K := by unfold metadataWordBound; nlinarith
  intro x hx
  apply metadata_size_le
  simp only [metadataEncodeWords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def metadataDecodeWords (K e : ℕ) := [e,K,K+1,e/(K+1),e%(K+1),0,1]

theorem metadata_decode_words (T K : ℕ) (e : Fin ((T+1)*(K+1))) :
    ∀ x∈metadataDecodeWords K e.val,x.size≤metadataWordBits T K := by
  have hb := metadataWordBound_basic T K
  have he := metadata_numbered_key T K e
  have hd := Nat.div_le_self e.val (K+1)
  have hm := Nat.mod_le e.val (K+1)
  intro x hx
  apply metadata_size_le
  simp only [metadataDecodeWords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

/-- Sorting and lookup never create keys: their comparison operands have
this Fin type even in temporary lists, so both sides fit this word size. -/
theorem metadata_key_comparison_bits (T K : ℕ) (e f : Fin ((T+1)*(K+1))) :
    e.val.size≤metadataWordBits T K ∧ f.val.size≤metadataWordBits T K :=
  ⟨metadata_size_le T K e.val (metadata_numbered_key T K e).le,
    metadata_size_le T K f.val (metadata_numbered_key T K f).le⟩

theorem metadata_live_index_bound (T K : ℕ) : standardLiveCap T K≤metadataWordBound T K := by
  have hd := metadata_depth_bound T (T+1) le_rfl
  unfold standardLiveCap metadataWordBound
  nlinarith [Nat.mul_le_mul_right (K+1) hd]

theorem metadata_live_index_bits (T K i : ℕ) (hi : i≤standardLiveCap T K) :
    i.size≤metadataWordBits T K := metadata_size_le T K i (hi.trans (metadata_live_index_bound T K))

theorem metadata_clock_bits (T K t : ℕ) (ht : t≤T) :
    t.size≤metadataWordBits T K ∧ (t+1).size≤metadataWordBits T K ∧ (t+2).size≤metadataWordBits T K := by
  have hb := (metadataWordBound_basic T K).1
  exact ⟨metadata_size_le T K t (by omega),metadata_size_le T K (t+1) (by omega),
    metadata_size_le T K (t+2) (by omega)⟩

theorem metadata_expanded_index_bits (T K t j : ℕ) (ht : t≤T+1)
    (hj : j≤5*(Nat.log 2 t+1)*(K+1)) : j.size≤metadataWordBits T K := by
  apply metadata_size_le
  have hd := metadata_depth_bound T t ht
  have hm := Nat.mul_le_mul_right (K+1) hd
  unfold metadataWordBound
  nlinarith

theorem metadata_candidate_index_bits (T K t j : ℕ) (ht : t≤T+1)
    (hj : j≤5*(Nat.log 2 t+1)) : j.size≤metadataWordBits T K :=
  metadata_expanded_index_bits T K t j ht (by nlinarith)

theorem actual_candidate_index_bits (T K t j : ℕ) (ht : t≤T+1)
    (hj : j≤(countedCandidateList t).1.length) : j.size≤metadataWordBits T K := by
  rw [countedCandidateList_length] at hj
  exact metadata_candidate_index_bits T K t j ht hj

theorem actual_expanded_index_bits (T K t j : ℕ) (ht : t≤T+1)
    (hj : j≤(countedFlatMap (countedHistoryKeys T K) (countedShortHistoryList t).1).1.length) :
    j.size≤metadataWordBits T K := by
  rw [countedExpandedLive_value,List.length_map] at hj
  exact metadata_expanded_index_bits T K t j ht (hj.trans (shortLiveList_length T K t))

theorem metadata_birth_comparison_bits (T K : ℕ) (i : Fin (T+1))
    (e : Fin ((T+1)*(K+1))) :
    i.val.size≤metadataWordBits T K ∧ (e.val/(K+1)).size≤metadataWordBits T K := by
  constructor
  · apply metadata_size_le
    have hi := i.isLt
    have hb := (metadataWordBound_basic T K).1
    omega
  · exact metadata_decode_words T K e _ (by simp [metadataDecodeWords])

theorem countedOrderedInsert_mem {α : Type} [LinearOrder α] (a b : α) (xs : List α) :
    b∈(countedOrderedInsert a xs).1 ↔ b=a ∨ b∈xs := by
  induction xs with
  | nil => simp [countedOrderedInsert]
  | cons c xs ih =>
    by_cases h : a≤c <;> simp [countedOrderedInsert,h,ih,or_left_comm]

theorem countedInsertionSort_mem {α : Type} [LinearOrder α] (xs : List α) (a : α) :
    a∈(countedInsertionSort xs).1 ↔ a∈xs := by
  induction xs with
  | nil => simp [countedInsertionSort]
  | cons b xs ih =>
    simp only [countedInsertionSort,countedOrderedInsert_mem,ih,List.mem_cons]

/-- The comparison operands encountered by the actual recursive insertion
routine, including the recursive suffix when insertion is delayed. -/
def insertionOperandsFit (B a : ℕ) : List ℕ→Prop
  | [] => a.size≤B
  | b::xs => a.size≤B ∧ b.size≤B ∧ (¬a≤b → insertionOperandsFit B a xs)

theorem insertionOperandsFit_of_mem (B a : ℕ) (xs : List ℕ) (ha : a.size≤B)
    (hxs : ∀ b∈xs,b.size≤B) : insertionOperandsFit B a xs := by
  induction xs with
  | nil => exact ha
  | cons b xs ih =>
    exact ⟨ha,hxs b (by simp),fun _=>ih (fun c hc=>hxs c (by simp [hc]))⟩

/-- Recursive insertion sorting calls the comparison routine on the
already sorted tail. Membership preservation certifies those intermediate
operands as well as the original input list. -/
def sortingOperandsFit (B : ℕ) : List ℕ→Prop
  | [] => True
  | a::xs => sortingOperandsFit B xs ∧ insertionOperandsFit B a (countedInsertionSort xs).1

theorem sortingOperandsFit_of_mem (B : ℕ) (xs : List ℕ)
    (hxs : ∀ a∈xs,a.size≤B) : sortingOperandsFit B xs := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    refine ⟨ih (fun b hb=>hxs b (by simp [hb])),?_⟩
    apply insertionOperandsFit_of_mem B a _ (hxs a (by simp))
    intro b hb
    exact hxs b (by simp [(countedInsertionSort_mem xs b).mp hb])

def dedupOperandsFit (B : ℕ) : List ℕ→Prop
  | [] => True
  | a::xs => dedupOperandsFit B xs ∧ a.size≤B ∧
      ∀ b∈(countedDedup xs).1,b.size≤B

theorem dedupOperandsFit_of_mem (B : ℕ) (xs : List ℕ)
    (hxs : ∀ a∈xs,a.size≤B) : dedupOperandsFit B xs := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    refine ⟨ih (fun b hb=>hxs b (by simp [hb])),hxs a (by simp),?_⟩
    intro b hb
    exact hxs b (by simp [(countedDedup_mem xs b).mp hb])

theorem actual_short_sort_intermediate_bits (T K t : ℕ) (ht : t≤T+1) :
    let xs := (countedFilter (countedActiveTest t) (countedCandidateList t).1).1
    dedupOperandsFit (metadataWordBits T K) xs ∧
      sortingOperandsFit (metadataWordBits T K) (countedDedup xs).1 := by
  dsimp only
  constructor
  · exact dedupOperandsFit_of_mem _ _ (actual_short_sort_operand_bits T K t ht)
  · apply sortingOperandsFit_of_mem
    intro a ha
    exact actual_short_sort_operand_bits T K t ht a ((countedDedup_mem _ a).mp ha)

end Paper254
#print axioms Paper254.metadataWordBound_lt_pow
#print axioms Paper254.metadata_log_words
#print axioms Paper254.metadata_power_prefix_words
#print axioms Paper254.actual_candidate_operand_bits
#print axioms Paper254.actual_active_operand_bits
#print axioms Paper254.metadata_encode_words
#print axioms Paper254.metadata_decode_words
#print axioms Paper254.metadata_key_comparison_bits
#print axioms Paper254.actual_expanded_index_bits
#print axioms Paper254.actual_short_sort_intermediate_bits

