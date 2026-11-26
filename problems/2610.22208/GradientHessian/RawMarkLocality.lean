import GradientHessian.RawLeafLocality

/-! Isolating one mark leaves every matrix, every memory direction, every
other leaf, and every other mark unchanged. Its b/a coefficients are the
literal mark injection and readout under the unchanged source matrix. -/

noncomputable section
namespace GradientHessian.RawMarkLocality
open RawHierarchy HigherHierarchy RawLeafFactor RawLeafLocality

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ t, MeasurableSpace (H t)]

theorem rest_eq_leaf_rest (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2) :
    (factor t i x).2=(factor t i y).2 :=
  congrArg (fun z : RawMarkFactor.Rest d n r J E H t => z.2.2) he

theorem rest_eq_matrix (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2) :
    (leafNumerical t x i).1=(leafNumerical t y i).1 := by
  rw [← RawMarkFactor.factor_matrix t i j,← RawMarkFactor.factor_matrix t i j]
  exact congrArg Prod.fst he

theorem rest_eq_other_mark (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2)
    (k : Fin (4096*J^2+1)) (hk : k≠j) :
    (leafNumerical t x i).2 k=(leafNumerical t y i).2 k := by
  obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq hk
  have hq := congrArg (fun z : RawMarkFactor.Rest d n r J E H t => z.2.1 q) he
  change (factor t i x).1.2 (j.succAbove q)=(factor t i y).1.2 (j.succAbove q) at hq
  simpa only [factor_target] using hq

theorem rest_eq_memory (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2) :
    memory t x=memory t y := RawLeafLocality.rest_eq_memory t i x y (rest_eq_leaf_rest t i j x y he)

theorem replace_memory (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (z : EuclideanSpace ℝ (Fin r)) (x : Raw d n r J E H t) :
    memory t (RawMarkFactor.replace t i j z x)=memory t x :=
  rest_eq_memory t i j _ _ (by simpa only using congrArg Prod.snd (RawMarkFactor.factor_replace t i j z x))

theorem replace_mark (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (z : EuclideanSpace ℝ (Fin r)) (x : Raw d n r J E H t) :
    (leafNumerical t (RawMarkFactor.replace t i j z x) i).2 j=z := by
  rw [← RawMarkFactor.factor_mark t i j,RawMarkFactor.factor_replace]

theorem replace_other_mark (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (z : EuclideanSpace ℝ (Fin r)) (x : Raw d n r J E H t)
    (k : Fin (4096*J^2+1)) (hk : k≠j) :
    (leafNumerical t (RawMarkFactor.replace t i j z x) i).2 k=(leafNumerical t x i).2 k :=
  rest_eq_other_mark t i j _ _ (by simpa only using congrArg Prod.snd (RawMarkFactor.factor_replace t i j z x)) k hk

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem rest_eq_other_leaf (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2)
    (q : LeafSlot t) (hq : q≠i) :
    leafData t (assemble P B fallback t x) q=leafData t (assemble P B fallback t y) q :=
  RawLeafLocality.rest_eq_other_leaf P B fallback t i x y (rest_eq_leaf_rest t i j x y he) q hq

theorem rest_eq_target_A (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2) :
    (leafData t (assemble P B fallback t x) i).A=(leafData t (assemble P B fallback t y) i).A := by
  rw [leaf_A_assemble,leaf_A_assemble,rest_eq_matrix t i j x y he]

theorem rest_eq_other_b (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2)
    (k : Fin (4096*J^2+1)) (hk : k≠j) :
    (leafData t (assemble P B fallback t x) i).b k=(leafData t (assemble P B fallback t y) i).b k := by
  rw [leaf_b_assemble,leaf_b_assemble,rest_eq_other_mark t i j x y he k hk]

theorem rest_eq_other_a (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (x y : Raw d n r J E H t)
    (he : (RawMarkFactor.factor t i j x).2=(RawMarkFactor.factor t i j y).2)
    (k : Fin (4096*J^2+1)) (hk : k≠j) :
    (leafData t (assemble P B fallback t x) i).a k=(leafData t (assemble P B fallback t y) i).a k := by
  rw [leaf_a_assemble,leaf_a_assemble,rest_eq_matrix t i j x y he,rest_eq_other_mark t i j x y he k hk]

theorem replace_target_b (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (z : EuclideanSpace ℝ (Fin r)) (x : Raw d n r J E H t) :
    (leafData t (assemble P B fallback t (RawMarkFactor.replace t i j z x)) i).b j=
      InverseGate.H₀ • LowRank.matrixEuclideanMap B z := by
  rw [leaf_b_assemble,replace_mark]

theorem replace_target_a (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (z : EuclideanSpace ℝ (Fin r)) (x : Raw d n r J E H t) :
    (leafData t (assemble P B fallback t (RawMarkFactor.replace t i j z x)) i).a j=
      UnmarkedReadout.sourceOutput J P (leafNumerical t x i).1 B fallback z := by
  rw [leaf_a_assemble,RawMarkFactor.replace_matrix,replace_mark]

end GradientHessian.RawMarkLocality
