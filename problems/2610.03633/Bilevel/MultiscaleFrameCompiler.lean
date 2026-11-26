import Bilevel.SingleFrameSourceProtocol
import Bilevel.MultiscaleDisclosedReply

/-! Actual old/new store compiler and its same-query energy certificate for
the macro-free SFO. Auxiliary genie columns do not enter the evaluator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
namespace Bilevel.MultiscaleMean
open SingleFrameSource ChiHierarchyIndex ChiHierarchyExecution ChiHierarchyHaar CompensatedMean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ}

def innerEvaluate (P : Parameters (E:=E) n) (p : ℝ) (q : InnerQuery E)
    (old new : SingleFrameSource.Store n E) (coin : Bool) : InnerReply E :=
  P.disclosedReply p old.1 new.1 (macroColumns n old) (macroColumns n new) q coin

def innerVector (_k : Fin 1) (q : InnerQuery E) : E := uProj E q.2

omit [CompleteSpace E] in
theorem innerVector_measurable [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace (LowerSpace E)] [BorelSpace (LowerSpace E)] (k : Fin 1) :
    Measurable (innerVector (E:=E) k) := (uProj E).continuous.measurable.comp measurable_snd

variable {D : ℕ}

def innerFrameReply (P : Parameters (E:=EuclideanGaussian.Space D) n) (p : ℝ)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D)
    (a : Orientations (counts n) 0 D) : InnerQuery (EuclideanGaussian.Space D) → Bool → InnerReply (EuclideanGaussian.Space D) :=
  innerOriginalReply (P.withFrame (frame hD a (Sum.inl ()))) p

def innerFrameLoss (P : Parameters (E:=EuclideanGaussian.Space D) n)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D)
    (a : Orientations (counts n) 0 D) : EuclideanGaussian.Space D → ℝ :=
  innerOriginalLoss (P.withFrame (frame hD a (Sum.inl ())))

theorem innerFrame_reply_from_energy (P : Parameters (E:=EuclideanGaussian.Space D) n) (p cap : ℝ)
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D) (hcap : 0≤cap)
    (hsmall : P.R*Real.sqrt cap≤P.signalResolution/2)
    (a : Orientations (counts n) 0 D) (r : ℕ) (q : InnerQuery (EuclideanGaussian.Space D)) (coin : Bool)
    (henergy : ∀ i : FrameIndex (counts n) 0,GenieProtocol.BoundedEnergy
      (sharedKnown (counts n) 0 D r (columns hD a) (Submodule.span ℝ (Set.range (fun k => innerVector k q))))
      (prefixSet (retained (counts n) 0 r i)) (columns hD a i) cap) :
    innerFrameReply P p hD a q coin=innerEvaluate P p q
      (actual (counts n) 0 r (columns hD a))
      (actual (counts n) 0 (r+if coin then 1 else 0) (columns hD a)) coin := by
  let W := sharedKnown (counts n) 0 D r (columns hD a)
    (Submodule.span ℝ (Set.range (fun k => innerVector k q)))
  have huW : uProj (EuclideanGaussian.Space D) q.2∈W :=
    Submodule.mem_sup_left (Submodule.subset_span ⟨(0:Fin 1),rfl⟩)
  have hold : ∀ k : Fin (n+1),k.val<r →
      macroColumns n (actual (counts n) 0 r (columns hD a)) k=
        (P.withFrame (frame hD a (Sum.inl ()))).U (ZeroChain.basis k) := by
    intro k hk
    exact (actual_macro n r (columns hD a) k hk).trans (frame_basis hD a (Sum.inl ()) k).symm
  have hnew : coin=true → ∀ k : Fin (n+1),k.val<r+1 →
      macroColumns n (actual (counts n) 0 (r+if coin then 1 else 0) (columns hD a)) k=
        (P.withFrame (frame hD a (Sum.inl ()))).U (ZeroChain.basis k) := by
    intro hb k hk
    subst coin
    exact (actual_macro n (r+1) (columns hD a) k hk).trans (frame_basis hD a (Sum.inl ()) k).symm
  have htail : ∀ k : Fin (n+1),r≤k.val →
      |WrappedChain.coordinates n P.R (frame hD a (Sum.inl ())) (uProj (EuclideanGaussian.Space D) q.2) k|<
        P.signalResolution := by
    intro k hk
    exact coordinate_small hD a r W P.R P.signalResolution cap (P.β_pos.trans_le P.β_le_R)
      P.signalResolution_pos hcap hsmall (henergy (Sum.inl ())) _ huW k hk
  exact (P.withFrame (frame hD a (Sum.inl ()))).original_eq_disclosed_reply p r _ _ coin hold hnew q htail

end Bilevel.MultiscaleMean
