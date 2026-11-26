import NCConcave16991.BranchOracleReply
import NCConcave16991.BranchOracleRequestSupport
import NCConcave16991.BranchOraclePrefix
import NCConcave16991.BranchOracleSourceProgram

/-! # Pointwise transport from actual frame births to chronological word support -/

namespace NCConcave16991.BranchOracle
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ)

abbrev DomainLedger := ∀ t : Vertex M m, Submodule ℝ (VertexLayer (ι := ι) E M m t)

def LedgerSupported (p : WordProfile ι) (W : Submodule ℝ E) (K : DomainLedger (ι := ι) E M m) : Prop :=
  ∀ t, K t ≤ wordSupport t.val (p.words t.val) W

theorem LedgerSupported.mono {p q : WordProfile ι} (hpq : WordProfile.WordsExtend p q)
    {W U : Submodule ℝ E} (hWU : W ≤ U) {K : DomainLedger (ι := ι) E M m}
    (hK : LedgerSupported E M m p W K) : LedgerSupported E M m q U K :=
  fun t ↦ (hK t).trans (wordSupport_mono (hpq t.val) hWU)

def ledgerBirth (K : DomainLedger (ι := ι) E M m) (t : Vertex M m)
    (a : VertexLayer (ι := ι) E M m t) : DomainLedger (ι := ι) E M m :=
  fun s ↦ K s ⊔ Submodule.span ℝ ({fillReply E M m t a s} : Set (VertexLayer (ι := ι) E M m s))

theorem ledgerBirth_supported (p : WordProfile ι) (W : Submodule ℝ E)
    (K : DomainLedger (ι := ι) E M m) (hK : LedgerSupported E M m p W K)
    (t : Vertex M m) (a : VertexLayer (ι := ι) E M m t)
    (ha : a ∈ wordSupport t.val (p.words t.val) W) :
    LedgerSupported E M m p W (ledgerBirth E M m K t a) := by
  intro s
  apply sup_le (hK s)
  apply Submodule.span_le.mpr
  intro z hz
  obtain rfl := Set.mem_singleton_iff.mp hz
  by_cases hs : s = t
  · subst s
    rw [fillReply_self]
    convert ha using 1
  · rw [fillReply_other E M m t s a hs]
    exact Submodule.zero_mem _

def RequestFormalSupported (p : WordProfile ι) (W : Submodule ℝ E) (q : MixedRequest (ι := ι) E M m) : Prop :=
  match q.2 with
  | Sum.inl a => a ∈ wordSupport q.1.val (p.words q.1.val) W
  | Sum.inr _ => True

def requestBirthVector (q : MixedRequest (ι := ι) E M m) (g : MixedReply (ι := ι) E M m) :
    VertexLayer (ι := ι) E M m q.1 :=
  match q.2 with
  | Sum.inl a => a
  | Sum.inr _ => g q.1

theorem requestBirth_supported (p : WordProfile ι) (W : Submodule ℝ E)
    (K K' : DomainLedger (ι := ι) E M m) (hK : LedgerSupported E M m p W K)
    (q : MixedRequest (ι := ι) E M m) (g : MixedReply (ι := ι) E M m)
    (hq : RequestFormalSupported E M m p W q)
    (hg : ∀ t w, g t w ∈ W)
    (hbirth : ∀ t, K' t ≤ ledgerBirth E M m K q.1 (requestBirthVector E M m q g) t) :
    LedgerSupported E M m p W K' := by
  have ha : requestBirthVector E M m q g ∈ wordSupport q.1.val (p.words q.1.val) W := by
    rcases q with ⟨t, a | b⟩
    · exact hq
    · exact all_coordinates_mem_wordSupport _ W (g t) (hg t)
  have hh := ledgerBirth_supported E M m p W K hK q.1 _ ha
  exact fun t ↦ (hbirth t).trans (hh t)

theorem inverseAnswer_supported (p : WordProfile ι) (W : Submodule ℝ E)
    (K : DomainLedger (ι := ι) E M m) (hK : LedgerSupported E M m p W K)
    (t : Vertex M m) (y : VertexLayer (ι := ι) E M m t) (hy : y ∈ K t) :
    y ∈ wordSupport t.val (p.words t.val) W := hK t hy

theorem finite_births_supported (p : WordProfile ι) (W : Submodule ℝ E)
    (K : ℕ → DomainLedger (ι := ι) E M m) (v : ℕ → MixedReply (ι := ι) E M m)
    (h0 : LedgerSupported E M m p W (K 0))
    (hv : ∀ k t, v k t ∈ wordSupport t.val (p.words t.val) W)
    (hbirth : ∀ k t, K (k + 1) t ≤ K k t ⊔ Submodule.span ℝ ({v k t} : Set (VertexLayer (ι := ι) E M m t)))
    (k : ℕ) : LedgerSupported E M m p W (K k) := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    intro t
    apply (hbirth k t).trans
    apply sup_le (ih t)
    apply Submodule.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact hv k t

theorem sourceRequest_formal_supported (p : WordProfile ι) (W : Submodule ℝ E) (r : ℕ)
    (hp : WordProfile.PrefixFilled p (r * (m + 1))) (t : Vertex M m) (e : E) :
    (if t.val ≤ r * (m + 1) then formalTarget E t.val e else 0) ∈ wordSupport t.val (p.words t.val) W := by
  split_ifs with ht
  · exact hp.target_mem ht W e
  · exact Submodule.zero_mem _

theorem queryRequest_fits (p : WordProfile ι) (W : Submodule ℝ E)
    (z : GlobalHard.Joint (MacroSpaces (ι := ι) E M m)) (t : Vertex M m) (slot : Fin 5) :
    RequestFormalSupported E M m p W (queryRequest E M m z t slot) := trivial

theorem forwardMatrixRequest_fits (p : WordProfile ι) (W : Submodule ℝ E)
    (marks : InverseMarks (ι := ι) E M m) (hm : InverseMarksSupported E M m p W marks)
    (i : ι) (j : Fin M) (k : Fin (m + 1)) :
    RequestFormalSupported E M m (p.matrixScheduleStep (fun _ ↦ i)) W
      (forwardMatrixRequest E M m marks i j k) := by
  convert forwardMatrixRequest_formal_supported E M m p W marks hm i j k using 1 <;> rfl

theorem transposeMatrixRequest_fits (p : WordProfile ι) (W : Submodule ℝ E)
    (marks : InverseMarks (ι := ι) E M m) (hm : InverseMarksSupported E M m p W marks)
    (i : ι) (j : Fin M) (k : Fin (m + 1)) :
    RequestFormalSupported E M m (p.matrixScheduleStep (fun _ ↦ i)) W
      (transposeMatrixRequest E M m marks i j k) := by
  convert transposeMatrixRequest_formal_supported E M m p W marks hm i j k using 1 <;> rfl

theorem sourceQueries_fits (p : WordProfile ι) (W : Submodule ℝ E) (r : ℕ) (e : E)
    (hp : WordProfile.PrefixFilled p (r * (m + 1))) (t : Vertex M m) :
    RequestFormalSupported E M m p W (sourceQueries E M m (r, e) t) :=
  sourceRequest_formal_supported E M m p W r hp t e

theorem outputRequest_fits (p : WordProfile ι) (W : Submodule ℝ E)
    (c : PrimalSpace (GlobalHardEuclidean.primalDimension (MacroSpaces (ι := ι) E M m))) (t : Vertex M m) :
    RequestFormalSupported E M m p W (outputRequest E M m c t) := trivial

end
end NCConcave16991.BranchOracle
