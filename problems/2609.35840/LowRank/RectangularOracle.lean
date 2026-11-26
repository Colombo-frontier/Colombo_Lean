import LowRank.BoundedTwoSidedPolicy
import LowRank.FiniteZeroPadding

/-! Rectangular two-sided queries carry their actual domain and reply
dimensions. An embedded square matrix can answer each such query with
one square query and a measurable, matrix-independent reply decoder. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

abbrev RectangularQuery (a b : ℕ) := (Fin b → ℝ) ⊕ (Fin a → ℝ)
abbrev RectangularReply (a b : ℕ) := (Fin a → ℝ) ⊕ (Fin b → ℝ)

def rectangularOracle {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    RectangularQuery a b → RectangularReply a b :=
  Sum.elim (fun v => Sum.inl (A *ᵥ v)) (fun v => Sum.inr (Aᵀ *ᵥ v))

theorem measurable_rectangularOracle (a b : ℕ) : Measurable
    (fun x : Matrix (Fin a) (Fin b) ℝ × RectangularQuery a b => rectangularOracle x.1 x.2) := by
  have hl : Measurable (fun x : Matrix (Fin a) (Fin b) ℝ × (Fin b → ℝ) =>
      Sum.inl (x.1 *ᵥ x.2) : _ → RectangularReply a b) := by
    apply measurable_inl.comp
    exact (show Continuous (fun x : Matrix (Fin a) (Fin b) ℝ × (Fin b → ℝ) =>
      x.1 *ᵥ x.2) by fun_prop).measurable
  have hr : Measurable (fun x : Matrix (Fin a) (Fin b) ℝ × (Fin a → ℝ) =>
      Sum.inr (x.1ᵀ *ᵥ x.2) : _ → RectangularReply a b) := by
    apply measurable_inr.comp
    exact (show Continuous (fun x : Matrix (Fin a) (Fin b) ℝ × (Fin a → ℝ) =>
      x.1ᵀ *ᵥ x.2) by fun_prop).measurable
  convert (hl.sumElim hr).comp
    (MeasurableEquiv.prodSumDistrib (Matrix (Fin a) (Fin b) ℝ) (Fin b → ℝ) (Fin a → ℝ)).measurable using 1
  funext x
  rcases x with ⟨A, v | v⟩ <;> rfl

def encodeEmbeddedQuery {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) :
    RectangularQuery a b → Bool × (Fin d → ℝ) :=
  Sum.elim (fun v => (false, Rᵀ *ᵥ v)) (fun v => (true, Lᵀ *ᵥ v))

def decodeEmbeddedReply {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ)
    (q : RectangularQuery a b) (w : Fin d → ℝ) : RectangularReply a b :=
  Sum.elim (fun _ => Sum.inl (L *ᵥ w)) (fun _ => Sum.inr (R *ᵥ w)) q

theorem measurable_encodeEmbeddedQuery {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) :
    Measurable (encodeEmbeddedQuery L R) := by
  apply Measurable.sumElim
  · exact measurable_const.prodMk (show Continuous (fun v : Fin b → ℝ => Rᵀ *ᵥ v) by fun_prop).measurable
  · exact measurable_const.prodMk (show Continuous (fun v : Fin a → ℝ => Lᵀ *ᵥ v) by fun_prop).measurable

theorem measurable_decodeEmbeddedReply {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ) :
    Measurable (fun x : RectangularQuery a b × (Fin d → ℝ) => decodeEmbeddedReply L R x.1 x.2) := by
  have hl : Measurable (fun x : (Fin b → ℝ) × (Fin d → ℝ) =>
      Sum.inl (L *ᵥ x.2) : _ → RectangularReply a b) :=
    measurable_inl.comp (show Continuous (fun x : (Fin b → ℝ) × (Fin d → ℝ) =>
      L *ᵥ x.2) by fun_prop).measurable
  have hr : Measurable (fun x : (Fin a → ℝ) × (Fin d → ℝ) =>
      Sum.inr (R *ᵥ x.2) : _ → RectangularReply a b) :=
    measurable_inr.comp (show Continuous (fun x : (Fin a → ℝ) × (Fin d → ℝ) =>
      R *ᵥ x.2) by fun_prop).measurable
  convert (hl.sumElim hr).comp
    (MeasurableEquiv.sumProdDistrib (Fin b → ℝ) (Fin a → ℝ) (Fin d → ℝ)).measurable using 1
  funext x
  rcases x with ⟨v | v, w⟩ <;> rfl

theorem embeddedOracle_reply {a b d : ℕ}
    (L : Matrix (Fin a) (Fin d) ℝ) (R : Matrix (Fin b) (Fin d) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (q : RectangularQuery a b) :
    decodeEmbeddedReply L R q (twoSidedOracle A (encodeEmbeddedQuery L R q)) =
      rectangularOracle (L * A * Rᵀ) q := by
  cases q <;>
    simp only [decodeEmbeddedReply, encodeEmbeddedQuery, rectangularOracle, Sum.elim_inl,
      Sum.elim_inr, twoSidedOracle, Bool.false_eq_true, if_false, if_true,
      Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mulVec_mulVec]

end
end LowRank
