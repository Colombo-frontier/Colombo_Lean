import RationalCompactMaster254
import HistoryBitCertificate254
import RationalMagnitude254
import RationalPredictionHeight254

noncomputable section
open scoped BigOperators
namespace Paper254

def EntryHeights {ι : Type*} (entries : List (ι×ℚ)) (b : ℕ) : Prop :=
  ∀ e∈entries,RationalHeight e.2 b

theorem EntryHeights.mono {ι : Type*} {entries : List (ι×ℚ)} {b c : ℕ}
    (h : EntryHeights entries b) (hbc : b≤c) : EntryHeights entries c :=
  fun e he=>(h e he).mono hbc

theorem RationalHeight.list_sum (xs : List ℚ) (b : ℕ)
    (hx : ∀ x∈xs,RationalHeight x b) : RationalHeight xs.sum (xs.length*(b+1)) := by
  induction xs with
  | nil => simpa using RationalHeight.zero
  | cons x xs ih =>
    have hh := (hx x (by simp)).add (ih (fun y hy=>hx y (by simp [hy])))
    simp only [List.sum_cons,List.length_cons]
    convert hh using 1 <;> ring

theorem rationalLookup_height {n b : ℕ} (entries : List (Fin n×ℚ))
    (h : EntryHeights entries b) (j : Fin n) : RationalHeight (rationalLookup entries j) b := by
  induction entries with
  | nil => exact RationalHeight.zero.mono (Nat.zero_le b)
  | cons e xs ih =>
    simp only [rationalLookup]
    split_ifs
    · exact h e (by simp)
    · exact ih (fun y hy=>h y (by simp [hy]))

def normalizeHeight (N b : ℕ) := b+N*(b+1)+1

theorem countedNormalize_height {n b : ℕ} (entries : List (Fin n×ℚ))
    (h : EntryHeights entries b) :
    EntryHeights (countedNormalize entries).1 (normalizeHeight entries.length b) := by
  have hsum := RationalHeight.list_sum (entries.map Prod.snd) b (by
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact h e he)
  simp only [List.length_map] at hsum
  intro e he
  rw [countedNormalize_value] at he
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
  exact (show RationalHeight (x.2*((entries.map Prod.snd).sum)⁻¹) _ from
    (h x hx).mul hsum.inv)

def NormalizeWorkHeights {n : ℕ} (entries : List (Fin n×ℚ)) (b : ℕ) : Prop :=
  EntryHeights entries b ∧
  (∀ xs : List ℚ,xs.Sublist (entries.map Prod.snd)→RationalHeight xs.sum b) ∧
  EntryHeights (countedNormalize entries).1 b

theorem NormalizeWorkHeights.mono {n b c : ℕ} {entries : List (Fin n×ℚ)}
    (h : NormalizeWorkHeights entries b) (hbc : b≤c) : NormalizeWorkHeights entries c :=
  ⟨h.1.mono hbc,fun xs hs=>(h.2.1 xs hs).mono hbc,h.2.2.mono hbc⟩

theorem normalize_work_heights {n b : ℕ} (entries : List (Fin n×ℚ))
    (h : EntryHeights entries b) : NormalizeWorkHeights entries (normalizeHeight entries.length b) := by
  refine ⟨h.mono (by dsimp [normalizeHeight]; omega),?_,countedNormalize_height entries h⟩
  intro xs hs
  have hh := RationalHeight.list_sum xs b (by
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp (hs.subset hx)
    exact h e he)
  apply hh.mono
  have hl := hs.length_le
  simp only [List.length_map] at hl
  have hm := Nat.mul_le_mul_right (b+1) hl
  dsimp [normalizeHeight]
  omega

theorem RationalHeight.dyadic_round {x : ℚ} {b : ℕ} (hx : RationalHeight x b) (p : ℕ) :
    RationalHeight (dyadicCeil p x) (b+1+p) :=
  dyadic_round_height (fun _ _ : Fin 1=>x) p b (fun _ _=>hx.real_abs)

def taylorWorkHeight (N b : ℕ) :=
  (N*(b+1)+N*N+1)+(N*(N*(b+1)+N*N+2))+b+N+3

def TaylorWorkHeights (x : ℚ) (N b : ℕ) : Prop :=
  ∀ t≤N,RationalHeight (countedTaylorState x t).1 b ∧
    RationalHeight (countedTaylorState x t).2.1 b ∧
    RationalHeight ((countedTaylorState x t).1*x) b ∧ RationalHeight (t+1:ℚ) b

theorem TaylorWorkHeights.mono {x : ℚ} {N b c : ℕ} (h : TaylorWorkHeights x N b)
    (hbc : b≤c) : TaylorWorkHeights x N c := by
  intro t ht
  have hh := h t ht
  exact ⟨hh.1.mono hbc,hh.2.1.mono hbc,hh.2.2.1.mono hbc,hh.2.2.2.mono hbc⟩

theorem taylor_work_heights (x : ℚ) (N b : ℕ) (hx : RationalHeight x b) :
    TaylorWorkHeights x N (taylorWorkHeight N b) := by
  intro t ht
  have hh := countedTaylorState_height x b t hx
  have hm := Nat.mul_le_mul_right (b+1) ht
  have hs := Nat.mul_le_mul ht ht
  have hl : t*(b+1)+t*t+2≤N*(b+1)+N*N+2 := by omega
  have hsum := Nat.mul_le_mul ht hl
  have hp := hh.1.mul hx
  have hi : RationalHeight (t+1:ℚ) (t+1) := by
    have hh := RationalHeight.of_int (t+1) (t+1) (by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast int_dim_le_pow (t+1))
    simpa using hh
  refine ⟨hh.1.mono ?_,hh.2.mono ?_,hp.mono ?_,hi.mono ?_⟩
  all_goals dsimp [taylorWorkHeight]; omega

def softmaxExpHeight (p b : ℕ) := (p+7)*((p+7)*(b+1)+(p+7)*(p+7)+2)
def softmaxRawHeight (p b : ℕ) := b+softmaxExpHeight p b+1
def softmaxNormalizedHeight (N p b : ℕ) := normalizeHeight N (softmaxRawHeight p b)
def softmaxUpperHeight (N p b : ℕ) := softmaxNormalizedHeight N p b+2*p+5
def softmaxOutputHeight (N p b : ℕ) := normalizeHeight N (softmaxUpperHeight N p b)
def softmaxWorkHeight (N p b : ℕ) :=
  b+taylorWorkHeight (p+7) b+softmaxExpHeight p b+softmaxRawHeight p b+
    softmaxNormalizedHeight N p b+softmaxUpperHeight N p b+softmaxOutputHeight N p b+p+10

def softmaxRawEntries {n : ℕ} (p : ℕ) (live : Finset (Fin n)) (w z : Fin n→ℚ) :=
  (live.sort (·≤·)).map (fun e=>(e,w e*rationalExp (z e) (p+4)))
def softmaxRoundedEntries {n : ℕ} (p : ℕ) (live : Finset (Fin n)) (w z : Fin n→ℚ) :=
  ((countedNormalize (softmaxRawEntries p live w z)).1).map (fun e=>(e.1,dyadicCeil (p+1) e.2))
def softmaxUpperEntries {n : ℕ} (p : ℕ) (live : Finset (Fin n)) (w z : Fin n→ℚ) :=
  (softmaxRoundedEntries p live w z).map (fun e=>(e.1,e.2+3/(2*(2:ℚ)^p)))

theorem countedLiveSoftmax_entries {n : ℕ} (p roundCost : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) :
    (countedLiveSoftmax p roundCost live w z).1=(countedNormalize (softmaxUpperEntries p live w z)).1 := by
  simp only [countedLiveSoftmax,mapWithCosts_values,countedRationalExp_value,countedRatPow_spec,
    softmaxUpperEntries,softmaxRoundedEntries,softmaxRawEntries,List.map_map,Function.comp_def]

def SoftmaxWorkHeights {n : ℕ} (p : ℕ) (live : Finset (Fin n)) (w z : Fin n→ℚ) (b : ℕ) : Prop :=
  (∀ j∈live,RationalHeight (w j) b ∧ RationalHeight (z j) b ∧ TaylorWorkHeights (z j) (p+7) b) ∧
  NormalizeWorkHeights (softmaxRawEntries p live w z) b ∧
  RationalHeight ((2:ℚ)^p) b ∧ RationalHeight (3/(2*(2:ℚ)^p)) b ∧
  EntryHeights (softmaxRoundedEntries p live w z) b ∧
  NormalizeWorkHeights (softmaxUpperEntries p live w z) b

theorem SoftmaxWorkHeights.mono {n p b c : ℕ} {live : Finset (Fin n)} {w z : Fin n→ℚ}
    (h : SoftmaxWorkHeights p live w z b) (hbc : b≤c) : SoftmaxWorkHeights p live w z c := by
  refine ⟨?_,h.2.1.mono hbc,h.2.2.1.mono hbc,h.2.2.2.1.mono hbc,
    h.2.2.2.2.1.mono hbc,h.2.2.2.2.2.mono hbc⟩
  intro j hj
  have hh := h.1 j hj
  exact ⟨hh.1.mono hbc,hh.2.1.mono hbc,hh.2.2.mono hbc⟩

theorem softmax_upper_entries_length {n : ℕ} (p : ℕ) (live : Finset (Fin n)) (w z : Fin n→ℚ) :
    (softmaxUpperEntries p live w z).length=live.card := by
  simp [softmaxUpperEntries,softmaxRoundedEntries,softmaxRawEntries,countedNormalize_length]

theorem softmax_work_heights {n b : ℕ} (p : ℕ) (live : Finset (Fin n)) (w z : Fin n→ℚ)
    (hw : ∀ j∈live,RationalHeight (w j) b) (hz : ∀ j∈live,RationalHeight (z j) b) :
    SoftmaxWorkHeights p live w z (softmaxWorkHeight live.card p b) ∧
    EntryHeights (countedLiveSoftmax p 1 live w z).1 (softmaxOutputHeight live.card p b) := by
  have he : ∀ j∈live,RationalHeight (rationalExp (z j) (p+4)) (softmaxExpHeight p b) := by
    intro j hj
    exact rationalTaylor_partial_height _ b (p+7) (hz j hj) (Finset.range (p+7)) (Finset.Subset.refl _)
  have hraw : EntryHeights (softmaxRawEntries p live w z) (softmaxRawHeight p b) := by
    intro e he0
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he0
    have hmem : j∈live := by simpa using hj
    exact (hw j hmem).mul (he j hmem)
  have hlen : (softmaxRawEntries p live w z).length=live.card := by simp [softmaxRawEntries]
  have hnorm := countedNormalize_height _ hraw
  rw [hlen] at hnorm
  have hrawWork := normalize_work_heights _ hraw
  rw [hlen] at hrawWork
  have hpow : RationalHeight ((2:ℚ)^p) p := by
    simpa using RationalHeight.of_int ((2:ℤ)^p) p (by simp)
  have hbump : RationalHeight (3/(2*(2:ℚ)^p)) (p+2) := by
    refine ⟨fun _ _=>3,(2:ℤ)^(p+1),by positivity,?_,?_,?_⟩
    · rw [abs_of_pos (by positivity : (0:ℤ)<2^(p+1))]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    · intros
      norm_num
      calc
        (3:ℤ)≤2^2 := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    · intros
      push_cast
      rw [pow_succ]
      ring
  have hrounded : EntryHeights (softmaxRoundedEntries p live w z)
      (softmaxNormalizedHeight live.card p b+p+2) := by
    intro e he0
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he0
    exact ((hnorm x hx).dyadic_round (p+1)).mono (by dsimp [softmaxNormalizedHeight]; omega)
  have hupper : EntryHeights (softmaxUpperEntries p live w z) (softmaxUpperHeight live.card p b) := by
    intro e he0
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he0
    exact ((hrounded x hx).add hbump).mono (by dsimp [softmaxUpperHeight]; omega)
  have hupperWork := normalize_work_heights _ hupper
  rw [softmax_upper_entries_length] at hupperWork
  refine ⟨⟨?_,hrawWork.mono ?_,hpow.mono ?_,hbump.mono ?_,hrounded.mono ?_,hupperWork.mono ?_⟩,?_⟩
  · intro j hj
    refine ⟨(hw j hj).mono ?_,(hz j hj).mono ?_,(taylor_work_heights _ (p+7) b (hz j hj)).mono ?_⟩
    all_goals dsimp [softmaxWorkHeight]; omega
  · dsimp [softmaxWorkHeight,softmaxNormalizedHeight]; omega
  · dsimp [softmaxWorkHeight]; omega
  · dsimp [softmaxWorkHeight]; omega
  · dsimp [softmaxWorkHeight,softmaxUpperHeight]; omega
  · dsimp [softmaxWorkHeight,softmaxOutputHeight]; omega
  · rw [countedLiveSoftmax_entries]
    simpa only [softmax_upper_entries_length] using countedNormalize_height _ hupper

def shareRawEntries {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ) (next : Finset (Fin n)) :=
  (next.sort (·≤·)).map (fun e=>(e,(1-alpha)*w e+alpha*prior e))

theorem countedPruneShare_entries {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ) (next : Finset (Fin n)) :
    (countedPruneShare w prior alpha next).1=(countedNormalize (shareRawEntries w prior alpha next)).1 := by
  simp [countedPruneShare,mapWithCosts_values,shareRawEntries]

def shareRawHeight (weightHeight inputHeight : ℕ) := weightHeight+3*inputHeight+4
def shareOutputHeight (N weightHeight inputHeight : ℕ) := normalizeHeight N (shareRawHeight weightHeight inputHeight)
def shareWorkHeight (N weightHeight inputHeight : ℕ) :=
  shareOutputHeight N weightHeight inputHeight+weightHeight+6*inputHeight+10

def PruneShareWorkHeights {n : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ) (next : Finset (Fin n)) (b : ℕ) : Prop :=
  RationalHeight alpha b ∧ RationalHeight (1-alpha) b ∧
  (∀ j∈next,RationalHeight (w j) b ∧ RationalHeight (prior j) b ∧
    RationalHeight ((1-alpha)*w j) b ∧ RationalHeight (alpha*prior j) b) ∧
  NormalizeWorkHeights (shareRawEntries w prior alpha next) b

theorem PruneShareWorkHeights.mono {n b c : ℕ} {w prior : Fin n→ℚ} {alpha : ℚ}
    {next : Finset (Fin n)} (h : PruneShareWorkHeights w prior alpha next b) (hbc : b≤c) :
    PruneShareWorkHeights w prior alpha next c := by
  refine ⟨h.1.mono hbc,h.2.1.mono hbc,?_,h.2.2.2.mono hbc⟩
  intro j hj
  have hh := h.2.2.1 j hj
  exact ⟨hh.1.mono hbc,hh.2.1.mono hbc,hh.2.2.1.mono hbc,hh.2.2.2.mono hbc⟩

theorem prune_share_work_heights {n b c : ℕ} (w prior : Fin n→ℚ) (alpha : ℚ)
    (next : Finset (Fin n)) (hw : ∀ j∈next,RationalHeight (w j) c)
    (hp : ∀ j∈next,RationalHeight (prior j) b) (ha : RationalHeight alpha b) :
    PruneShareWorkHeights w prior alpha next (shareWorkHeight next.card c b) ∧
    EntryHeights (countedPruneShare w prior alpha next).1 (shareOutputHeight next.card c b) := by
  have hsub := RationalHeight.one.sub ha
  have hraw : EntryHeights (shareRawEntries w prior alpha next) (shareRawHeight c b) := by
    intro e he
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hj' : j∈next := by simpa using hj
    exact ((hsub.mul (hw j hj')).add (ha.mul (hp j hj'))).mono (by dsimp [shareRawHeight]; omega)
  have hlen : (shareRawEntries w prior alpha next).length=next.card := by simp [shareRawEntries]
  have hwork := normalize_work_heights _ hraw
  rw [hlen] at hwork
  refine ⟨⟨ha.mono ?_,hsub.mono ?_,?_,hwork.mono ?_⟩,?_⟩
  · dsimp [shareWorkHeight]; omega
  · dsimp [shareWorkHeight]; omega
  · intro j hj
    refine ⟨(hw j hj).mono ?_,(hp j hj).mono ?_,(hsub.mul (hw j hj)).mono ?_,(ha.mul (hp j hj)).mono ?_⟩
    all_goals dsimp [shareWorkHeight]; omega
  · dsimp [shareWorkHeight,shareOutputHeight]; omega
  · rw [countedPruneShare_entries]
    simpa only [hlen] using countedNormalize_height _ hraw

def masterOutputHeight (N M p b : ℕ) :=
  softmaxOutputHeight M p (shareOutputHeight M (softmaxOutputHeight N p b) b)
def masterWorkHeight (N M p b : ℕ) :=
  softmaxWorkHeight N p b+shareWorkHeight M (softmaxOutputHeight N p b) b+
    softmaxWorkHeight M p (shareOutputHeight M (softmaxOutputHeight N p b) b)+
    masterOutputHeight N M p b+b+p+10

def MasterWorkHeights {n : ℕ} (p : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) (b : ℕ) : Prop :=
  let weighted := (countedLiveSoftmax p 1 live w z).1
  let shared := (countedPruneShare (rationalLookup weighted) prior alpha next).1
  SoftmaxWorkHeights p live w z b ∧
  PruneShareWorkHeights (rationalLookup weighted) prior alpha next b ∧
  SoftmaxWorkHeights p next (rationalLookup shared) (fun _=>0) b ∧
  EntryHeights (countedMasterUpdate p 1 live next w z prior alpha).1 b

theorem MasterWorkHeights.mono {n p b c : ℕ} {live next : Finset (Fin n)}
    {w z prior : Fin n→ℚ} {alpha : ℚ} (h : MasterWorkHeights p live next w z prior alpha b)
    (hbc : b≤c) : MasterWorkHeights p live next w z prior alpha c :=
  ⟨h.1.mono hbc,h.2.1.mono hbc,h.2.2.1.mono hbc,h.2.2.2.mono hbc⟩

theorem master_work_heights {n b : ℕ} (p : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ)
    (hw : ∀ j∈live,RationalHeight (w j) b) (hz : ∀ j∈live,RationalHeight (z j) b)
    (hp : ∀ j∈next,RationalHeight (prior j) b) (ha : RationalHeight alpha b) :
    MasterWorkHeights p live next w z prior alpha (masterWorkHeight live.card next.card p b) := by
  have hfirst := softmax_work_heights p live w z hw hz
  have hshare := prune_share_work_heights
    (rationalLookup (countedLiveSoftmax p 1 live w z).1) prior alpha next
    (fun j _=>rationalLookup_height _ hfirst.2 j) hp ha
  have hlast := softmax_work_heights p next
    (rationalLookup (countedPruneShare (rationalLookup (countedLiveSoftmax p 1 live w z).1) prior alpha next).1)
    (fun _=>0) (fun j _=>rationalLookup_height _ hshare.2 j)
    (fun _ _=>RationalHeight.zero.mono (Nat.zero_le _))
  refine ⟨hfirst.1.mono ?_,hshare.1.mono ?_,hlast.1.mono ?_,hlast.2.mono ?_⟩
  all_goals dsimp [masterWorkHeight,masterOutputHeight]; omega

end Paper254
#print axioms Paper254.softmax_work_heights
#print axioms Paper254.master_work_heights
