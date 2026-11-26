import LowRank.MeasurableQueryDirection
import LowRank.FactorReply
import LowRank.VisibleOraclePolicy

/-! Reduce any ambient query to one unit query in the unexposed coordinates.
The contribution of exposed coordinates is computed from visible A,C,B.
All formulas are total and measurable, including zero-residual inputs. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

def headQueryCoordinates {d q r : ℕ} (vis : VisibleFactorData d q r) (v : Fin d → ℝ) : Fin q → ℝ :=
  fun i => (vis.2ᵀ *ᵥ v) (Sum.inl i)

def tailQueryCoordinates {d q r : ℕ} (vis : VisibleFactorData d q r) (v : Fin d → ℝ) : Fin r → ℝ :=
  fun i => (vis.2ᵀ *ᵥ v) (Sum.inr i)

def exposedQueryReply {d q r : ℕ} (vis : VisibleFactorData d q r) (x : Fin q → ℝ) : Fin d → ℝ :=
  vis.2 *ᵥ Sum.elim (vis.1.1 *ᵥ (vis.1.1ᵀ *ᵥ x)) (vis.1.2 *ᵥ (vis.1.1ᵀ *ᵥ x))

theorem block_exposed_query_reply {q r s : ℕ} (A : Matrix (Fin q) (Fin q) ℝ)
    (C : Matrix (Fin r) (Fin q) ℝ) (D : Matrix (Fin r) (Fin s) ℝ) (x : Fin q → ℝ) :
    (fromBlocks A 0 C D * (fromBlocks A 0 C D)ᵀ) *ᵥ Sum.elim x 0 =
      Sum.elim (A *ᵥ (Aᵀ *ᵥ x)) (C *ᵥ (Aᵀ *ᵥ x)) := by
  rw [exposed_gram_blocks, fromBlocks_mulVec]
  simp [Matrix.mulVec_mulVec]

theorem ambient_query_split {d q r : ℕ} (vis : VisibleFactorData d q r)
    (hB : vis.2 * vis.2ᵀ = 1) (v : Fin d → ℝ) :
    vis.2 *ᵥ Sum.elim (headQueryCoordinates vis v) 0 +
      ambientQuery vis (tailQueryCoordinates vis v) = v := by
  rw [ambientQuery, ← Matrix.mulVec_add]
  have hz : Sum.elim (headQueryCoordinates vis v) (0 : Fin r → ℝ) +
      Sum.elim (0 : Fin q → ℝ) (tailQueryCoordinates vis v) = vis.2ᵀ *ᵥ v := by
    funext i
    cases i <;> simp [headQueryCoordinates, tailQueryCoordinates]
  rw [hz, Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {d t q r s : ℕ}

def reducedQueryDirection (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (vis : VisibleFactorData d q (r + 1)) (v : Fin d → ℝ) : Fin (r + 1) → ℝ :=
  unitCoordinateDirection b (tailQueryCoordinates vis v)

def decodeReducedQuery (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (vis : VisibleFactorData d q (r + 1)) (v reply : Fin d → ℝ) : Fin d → ℝ :=
  exposedQueryReply vis (headQueryCoordinates vis v) +
    coordinateSize b (tailQueryCoordinates vis v) • reply

theorem reducedQueryDirection_norm (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (vis : VisibleFactorData d q (r + 1)) (v : Fin d → ℝ) :
    ‖(basisCoordinates b).symm (reducedQueryDirection b vis v)‖ = 1 :=
  unitCoordinateDirection_norm b _

theorem ambientQuery_scaled_direction (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (vis : VisibleFactorData d q (r + 1)) (v : Fin d → ℝ) :
    coordinateSize b (tailQueryCoordinates vis v) • ambientQuery vis (reducedQueryDirection b vis v) =
      ambientQuery vis (tailQueryCoordinates vis v) := by
  change coordinateSize b (tailQueryCoordinates vis v) •
    (vis.2 *ᵥ Sum.elim 0 (reducedQueryDirection b vis v)) =
      vis.2 *ᵥ Sum.elim 0 (tailQueryCoordinates vis v)
  rw [← Matrix.mulVec_smul]
  apply congrArg (fun z : Fin q ⊕ Fin (r + 1) → ℝ => vis.2 *ᵥ z)
  have h := coordinateSize_smul_direction b (tailQueryCoordinates vis v)
  funext i
  cases i with
  | inl i => simp
  | inr i => exact congrFun h i

theorem decodeReducedQuery_eq (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (st : FactorData d t q (r + 1) s) (D : Matrix (Fin (r + 1)) (Fin s) ℝ)
    (hst : st.Orthogonal) (v : Fin d → ℝ) :
    let X := representedMatrix st D
    let W := X * Xᵀ
    let vis := visibleFactorData st
    decodeReducedQuery b vis v (W *ᵥ ambientQuery vis (reducedQueryDirection b vis v)) = W *ᵥ v := by
  dsimp only
  let vis := visibleFactorData st
  let W := representedMatrix st D * (representedMatrix st D)ᵀ
  have hk : W *ᵥ (vis.2 *ᵥ Sum.elim (headQueryCoordinates vis v) 0) =
      exposedQueryReply vis (headQueryCoordinates vis v) := by
    change (representedMatrix st D * (representedMatrix st D)ᵀ) *ᵥ
      (st.2.1 *ᵥ Sum.elim (headQueryCoordinates vis v) 0) = _
    rw [representedMatrix_reply st D _ hst.1 hst.2.2.1, block_exposed_query_reply]
    rfl
  change exposedQueryReply vis (headQueryCoordinates vis v) +
    coordinateSize b (tailQueryCoordinates vis v) •
      (W *ᵥ ambientQuery vis (reducedQueryDirection b vis v)) = W *ᵥ v
  rw [← hk, ← Matrix.mulVec_smul, ambientQuery_scaled_direction, ← Matrix.mulVec_add,
    ambient_query_split vis hst.2.1 v]

theorem measurable_headQueryCoordinates {S : Type*} [MeasurableSpace S]
    (vis : S → VisibleFactorData d q r) (v : S → Fin d → ℝ)
    (hvis : Measurable vis) (hv : Measurable v) :
    Measurable (fun x => headQueryCoordinates (vis x) (v x)) := by
  apply measurable_pi_lambda
  intro i
  simp only [headQueryCoordinates, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  fun_prop

theorem measurable_tailQueryCoordinates {S : Type*} [MeasurableSpace S]
    (vis : S → VisibleFactorData d q r) (v : S → Fin d → ℝ)
    (hvis : Measurable vis) (hv : Measurable v) :
    Measurable (fun x => tailQueryCoordinates (vis x) (v x)) := by
  apply measurable_pi_lambda
  intro i
  simp only [tailQueryCoordinates, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  fun_prop

theorem measurable_exposedQueryReply {S : Type*} [MeasurableSpace S]
    (vis : S → VisibleFactorData d q r) (x : S → Fin q → ℝ)
    (hvis : Measurable vis) (hx : Measurable x) :
    Measurable (fun z => exposedQueryReply (vis z) (x z)) := by
  have ht : Measurable (fun z => (vis z).1.1 *ᵥ ((vis z).1.1ᵀ *ᵥ x z)) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    fun_prop
  have hb : Measurable (fun z => (vis z).1.2 *ᵥ ((vis z).1.1ᵀ *ᵥ x z)) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    fun_prop
  have hm : Measurable (fun z => Sum.elim ((vis z).1.1 *ᵥ ((vis z).1.1ᵀ *ᵥ x z))
      ((vis z).1.2 *ᵥ ((vis z).1.1ᵀ *ᵥ x z))) := by
    apply measurable_pi_lambda
    intro i
    cases i with
    | inl i => exact (measurable_pi_apply i).comp ht
    | inr i => exact (measurable_pi_apply i).comp hb
  unfold exposedQueryReply
  apply measurable_pi_lambda
  intro i
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

theorem measurable_reducedQueryDirection {S : Type*} [MeasurableSpace S]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (vis : S → VisibleFactorData d q (r + 1)) (v : S → Fin d → ℝ)
    (hvis : Measurable vis) (hv : Measurable v) :
    Measurable (fun x => reducedQueryDirection b (vis x) (v x)) :=
  (measurable_unitCoordinateDirection b).comp (measurable_tailQueryCoordinates vis v hvis hv)

theorem measurable_decodeReducedQuery {S : Type*} [MeasurableSpace S]
    (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (vis : S → VisibleFactorData d q (r + 1)) (v reply : S → Fin d → ℝ)
    (hvis : Measurable vis) (hv : Measurable v) (hr : Measurable reply) :
    Measurable (fun x => decodeReducedQuery b (vis x) (v x) (reply x)) :=
  (measurable_exposedQueryReply vis _ hvis (measurable_headQueryCoordinates vis v hvis hv)).add
    (((measurable_coordinateSize b).comp (measurable_tailQueryCoordinates vis v hvis hv)).smul hr)

end
end LowRank
