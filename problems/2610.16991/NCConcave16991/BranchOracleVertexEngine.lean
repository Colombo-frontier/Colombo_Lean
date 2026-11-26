import NCConcave16991.BranchOracleEngine
import NCConcave16991.BranchOracleNativeLedger
import NCConcave16991.MixedHaarVertexStep
import NCConcave16991.MixedHaarVertexInitial
import NCConcave16991.MixedHaarProgramStream

/-! # The literal native Gaussian stream is a chronological word engine -/

namespace NCConcave16991.BranchOracle
noncomputable section
open MixedHaar

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

theorem nativeLocalStep_selected {I : Type*} [Fintype I] (F : I → Type*)
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)] [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
    (i : I) (s : FrameState (nativeDimension F i)) (q : F i ⊕ F i) (g : F i) :
    nativeLocalStep F i s ⟨i, q⟩ g = nativeSafeFrameStep (nativeCoordinates F i) s q g := by
  simp only [nativeLocalStep, if_pos rfl, nativeCoordinateRequest, nativeRequestAt, dif_pos rfl]
  rfl

theorem nativePartialDomain_initial {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {k : ℕ} (C : F ≃ₗᵢ[ℝ] Space k) : nativePartialDomain C (initialFrameState k) = ⊥ := by
  have hp : prefixSpan (0 : Fin (k + 1)) = ⊥ := by
    apply le_antisymm
    · intro x hx
      change x = 0
      have hh := (mem_prefixSpan_iff_coordinates (0 : Fin (k + 1)) x).mp hx
      ext i
      exact hh i (Nat.zero_le i.val)
    · exact bot_le
  change ((prefixSpan (0 : Fin (k + 1))).map _).map _ = ⊥
  rw [hp, Submodule.map_bot, Submodule.map_bot]

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ)

abbrev NativeWordFamily := fun t : Vertex M m ↦ VertexLayer (ι := ι) E M m t
abbrev NativeWordFrames := VertexFrame (nativeDimension (NativeWordFamily (ι := ι) E M m))
abbrev NativeWordStream := NativeWordFrames (ι := ι) E M m × List (MixedReply (ι := ι) E M m)

def vertexLedger (frames : NativeWordFrames (ι := ι) E M m) : DomainLedger (ι := ι) E M m :=
  fun t ↦ nativePartialDomain (nativeCoordinates (NativeWordFamily (ι := ι) E M m) t) (frames t)

theorem vertexStep_ledger_le (frames : NativeWordFrames (ι := ι) E M m)
    (q : MixedRequest (ι := ι) E M m) (g : MixedReply (ι := ι) E M m) (t : Vertex M m) :
    vertexLedger E M m (vertexStep (NativeWordFamily (ι := ι) E M m) frames q g).1 t ≤
      ledgerBirth E M m (vertexLedger E M m frames) q.1 (requestBirthVector E M m q g) t := by
  classical
  rcases q with ⟨v, a⟩
  by_cases h : v = t
  · subst t
    change nativePartialDomain _ (nativeLocalStep (NativeWordFamily (ι := ι) E M m) v (frames v) ⟨v, a⟩ (g v)).1 ≤ _
    rw [nativeLocalStep_selected]
    change nativePartialDomain _ (nativeSafeFrameStep _ (frames v) a (g v)).1 ≤
      nativePartialDomain _ (frames v) ⊔ Submodule.span ℝ ({fillReply E M m v (requestBirthVector E M m ⟨v,a⟩ g) v} : Set _)
    rw [fillReply_self]
    convert nativeSafeFrameStep_domain_le (nativeCoordinates (NativeWordFamily (ι := ι) E M m) v) (frames v) a (g v) using 1
    cases a <;> rfl
  · change nativePartialDomain _ (nativeLocalStep (NativeWordFamily (ι := ι) E M m) t (frames t) ⟨v, a⟩ (g t)).1 ≤ _
    simp only [nativeLocalStep, if_neg h]
    exact le_sup_left

theorem vertexStep_inverse_reply_mem (frames : NativeWordFrames (ι := ι) E M m)
    (t : Vertex M m) (b : VertexLayer (ι := ι) E M m t) (g : MixedReply (ι := ι) E M m) :
    (vertexStep (NativeWordFamily (ι := ι) E M m) frames ⟨t, Sum.inr b⟩ g).2 t ∈
      vertexLedger E M m frames t ⊔ Submodule.span ℝ ({g t} : Set _) := by
  change (nativeLocalStep (NativeWordFamily (ι := ι) E M m) t (frames t) ⟨t, Sum.inr b⟩ (g t)).2 ∈ _
  rw [nativeLocalStep_selected]
  exact nativeSafeInverseAnswer_mem_old_sup_gaussian _ _ _ _

def wordStreamOracle : NativeWordStream (ι := ι) E M m → MixedRequest (ι := ι) E M m →
    NativeWordStream (ι := ι) E M m × MixedReply (ι := ι) E M m :=
  streamOracle (vertexStep (NativeWordFamily (ι := ι) E M m)) (0 : MixedReply (ι := ι) E M m)

def wordStreamGaussian (s : NativeWordStream (ι := ι) E M m) : MixedReply (ι := ι) E M m := s.2.headD 0

def wordStreamAdmissible (W : Submodule ℝ E) (s : NativeWordStream (ι := ι) E M m) : Prop :=
  ∀ g ∈ s.2, ∀ t w, g t w ∈ W

def streamWordEngine (W : Submodule ℝ E) : WordEngine (ι := ι) E M m (NativeWordStream (ι := ι) E M m) where
  ledger s := vertexLedger E M m s.1
  oracle := wordStreamOracle E M m
  gaussian := wordStreamGaussian E M m
  admissible := wordStreamAdmissible E M m W
  admissible_step := by
    intro s q hs
    rcases s with ⟨frames, draws⟩
    cases draws with
    | nil => intro g hg; exact (List.not_mem_nil hg).elim
    | cons g gs => intro h hh; exact hs h (List.mem_cons_of_mem g hh)
  domain_le := by
    intro s q t
    rcases s with ⟨frames, draws⟩
    cases draws with
    | nil => convert vertexStep_ledger_le E M m frames q 0 t using 1 <;> rfl
    | cons g gs => convert vertexStep_ledger_le E M m frames q g t using 1 <;> rfl
  inverse_reply_mem := by
    intro s t b
    rcases s with ⟨frames, draws⟩
    cases draws with
    | nil => convert vertexStep_inverse_reply_mem E M m frames t b 0 using 1 <;> rfl
    | cons g gs => convert vertexStep_inverse_reply_mem E M m frames t b g using 1 <;> rfl

theorem streamWordEngine_covered (W : Submodule ℝ E) : (streamWordEngine (ι := ι) E M m W).Covered W := by
  intro s hs t w
  rcases s with ⟨frames, draws⟩
  cases draws with
  | nil => change (0 : E) ∈ W; exact W.zero_mem
  | cons g gs => exact hs g (List.mem_cons_self) t w

theorem streamWordEngine_initial_supported (W : Submodule ℝ E) (draws : List (MixedReply (ι := ι) E M m))
    (p : WordProfile ι) : LedgerSupported E M m p W
      ((streamWordEngine E M m W).ledger (initialVertexFrame (nativeDimension (NativeWordFamily (ι := ι) E M m)), draws)) := by
  intro t
  change nativePartialDomain _ (initialFrameState _) ≤ _
  rw [nativePartialDomain_initial]
  exact bot_le

end
end NCConcave16991.BranchOracle
