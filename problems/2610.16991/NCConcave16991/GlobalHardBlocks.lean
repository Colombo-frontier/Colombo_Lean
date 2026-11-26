import NCConcave16991.GlobalHardCoordinates
import NCConcave16991.HessianOverlap

/-! # Actual orthogonal blocks, coordinate contractions and local supports -/

namespace NCConcave16991.GlobalHard

universe u

noncomputable section

open scoped BigOperators InnerProductSpace

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

variable {M N : ℕ} (V : Fin M → Fin (N + 1) → Type u)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]

def BlockFamily (q : Fin M ⊕ Fin M) : Type u :=
  match q with
  | Sum.inl j => PrimalStage V j
  | Sum.inr j => PipeSmoothness.Layers (V j)

instance (priority := 50) blockNormed (j : Fin M ⊕ Fin M) : NormedAddCommGroup (BlockFamily V j) := by
  cases j <;> dsimp [BlockFamily] <;> infer_instance

instance (priority := 50) blockInner (j : Fin M ⊕ Fin M) : InnerProductSpace ℝ (BlockFamily V j) := by
  cases j <;> dsimp [BlockFamily] <;> infer_instance

instance (priority := 50) blockComplete (j : Fin M ⊕ Fin M) : CompleteSpace (BlockFamily V j) := by
  cases j <;> dsimp [BlockFamily] <;> infer_instance

abbrev Blocks := PiLp 2 (BlockFamily V)

def regroup : Blocks V ≃ₗᵢ[ℝ] Joint V :=
  PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (BlockFamily V)

def support (j : Fin M) : Finset (Fin M ⊕ Fin M) :=
  {Sum.inl j, Sum.inr j} ∪ Finset.univ.filter (fun q ↦ ∃ k : Fin M, q = Sum.inl k ∧ k.val + 1 = j.val)

theorem mem_support_inl (j k : Fin M) : Sum.inl k ∈ support j ↔ k = j ∨ k.val + 1 = j.val := by
  simp [support]

theorem mem_support_inr (j k : Fin M) : Sum.inr k ∈ support j ↔ k = j := by
  simp [support]

theorem support_degree (q : Fin M ⊕ Fin M) :
    (Finset.univ.filter (fun j : Fin M ↦ q ∈ support j)).card ≤ 2 := by
  classical
  cases q with
  | inr k =>
      have he : Finset.univ.filter (fun j : Fin M ↦ Sum.inr k ∈ support j) = {k} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_support_inr, Finset.mem_singleton]
        exact eq_comm
      rw [he]
      norm_num
  | inl k =>
      by_cases hk : k.val + 1 < M
      · let next : Fin M := ⟨k.val + 1, hk⟩
        have hs : Finset.univ.filter (fun j : Fin M ↦ Sum.inl k ∈ support j) ⊆ {k, next} := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_support_inl] at hj
          rcases hj with h | h
          · simp [h]
          · have he : j = next := Fin.ext h.symm
            simp [he]
        exact (Finset.card_le_card hs).trans (by
          have hh := Finset.card_insert_le k ({next} : Finset (Fin M))
          simpa using hh)
      · have hs : Finset.univ.filter (fun j : Fin M ↦ Sum.inl k ∈ support j) ⊆ {k} := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_support_inl] at hj
          rcases hj with h | h
          · simp [h]
          · omega
        exact (Finset.card_le_card hs).trans (by norm_num)

end

end NCConcave16991.GlobalHard
