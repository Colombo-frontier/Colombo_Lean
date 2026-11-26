import SecondOrder.SeededOracleCollection

open MeasureTheory ProbabilityTheory

namespace SecondOrder
namespace OracleProgram
noncomputable section
open scoped Classical

variable {I Q Y O Ω S T : Type} [MeasurableSpace Q] [MeasurableSpace Y]
  [MeasurableSpace O] [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]

def collectSeedTailProgram (o₀ : O) (p : I → S → OracleProgram Q Y O) (i : I) (is : List I)
    (w : O × (Fin is.length → S)) : OracleProgram Q Y (I → O) :=
  bind (collectSeedList o₀ p is w.2) (fun os => .done (Function.update os i w.1))

theorem collectSeedTailProgram_measurable (q₀ : Q) (o₀ : O) (p : I → S → OracleProgram Q Y O)
    (hp : ∀ i, MeasurableFamily q₀ o₀ (p i)) (i : I) (is : List I) :
    MeasurableFamily q₀ (fun _ => o₀) (collectSeedTailProgram o₀ p i is) := by
  apply ((collectSeedList_measurable q₀ o₀ p hp is).comp
    (fun w : O × (Fin is.length → S) => w.2) measurable_snd).bind
  apply measurableFamily_done
  exact (measurable_update_reply i).comp (measurable_fst.fst.prodMk measurable_snd)

theorem collectSeedTailProgram_usesAtMost (o₀ : O) (p : I → S → OracleProgram Q Y O)
    (cost : I → ℕ) (hp : ∀ i s, UsesAtMost (cost i) (p i s)) (i : I) (is : List I)
    (w : O × (Fin is.length → S)) :
    UsesAtMost ((is.map cost).sum) (collectSeedTailProgram o₀ p i is w) := by
  have hh := usesAtMost_bind (collectSeedList_usesAtMost o₀ p cost hp is w.2)
    (fun os => .done (Function.update os i w.1)) (m := 0) (fun _ => trivial)
  simpa only [Nat.add_zero] using hh

theorem collectSeedTailProgram_kernel (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : I → S → OracleProgram Q Y O) (hp : ∀ i, MeasurableFamily q₀ o₀ (p i))
    (cost : I → ℕ) (hcost : ∀ i s, UsesAtMost (cost i) (p i s)) (i : I) (is : List I) (o : O) :
    seededOutputKernel μ (Measure.pi (fun _ : Fin is.length => η)) q₀ y₀ (fun _ => o₀) a₀ reply hr
      (collectSeedTailProgram o₀ p i is) (collectSeedTailProgram_measurable q₀ o₀ p hp i is)
      ((is.map cost).sum) o=
      Measure.map (fun os => Function.update os i o)
        (seededOutputLaw μ (Measure.pi (fun _ : Fin is.length => η)) q₀ (fun _ => o₀) reply
          (collectSeedList o₀ p is) ((is.map cost).sum)) := by
  exact seededOutputLaw_bind_done μ (Measure.pi (fun _ : Fin is.length => η)) q₀ y₀
    (fun _ => o₀) (fun _ => o₀) a₀ reply hr (collectSeedList o₀ p is)
    (collectSeedList_measurable q₀ o₀ p hp is) ((is.map cost).sum)
    (collectSeedList_usesAtMost o₀ p cost hcost is) _
    ((measurable_update_reply i).comp (measurable_const.prodMk measurable_id))

theorem collectSeedList_outputLaw_cons (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : I → S → OracleProgram Q Y O) (hp : ∀ i, MeasurableFamily q₀ o₀ (p i))
    (cost : I → ℕ) (hcost : ∀ i s, UsesAtMost (cost i) (p i s)) (i : I) (is : List I) :
    seededOutputLaw μ (Measure.pi (fun _ : Fin (i::is).length => η)) q₀ (fun _ => o₀) reply
      (collectSeedList o₀ p (i::is)) (((i::is).map cost).sum)=
      (seededOutputLaw μ η q₀ o₀ reply (p i) (cost i)).bind
        (seededOutputKernel μ (Measure.pi (fun _ : Fin is.length => η)) q₀ y₀ (fun _ => o₀) a₀ reply hr
          (collectSeedTailProgram o₀ p i is) (collectSeedTailProgram_measurable q₀ o₀ p hp i is)
          ((is.map cost).sum)) := by
  have hg := finCons_measurePreserving is.length (fun _ => η)
  have hs := seededOutputLaw_mapSeed μ (η.prod (Measure.pi (fun _ : Fin is.length => η)))
    q₀ y₀ (fun _ => o₀) a₀ reply hr (collectSeedList o₀ p (i::is))
    (collectSeedList_measurable q₀ o₀ p hp (i::is))
    (fun w : S × (Fin is.length → S) => Fin.cons w.1 w.2) hg.measurable
    (cost i+(is.map cost).sum)
  rw [hg.map_eq] at hs
  have he : (fun w : S × (Fin is.length → S) => collectSeedList o₀ p (i::is) (Fin.cons w.1 w.2))=
      (fun w : S × (Fin is.length → S) => bind (p i w.1) (fun o => collectSeedTailProgram o₀ p i is (o,w.2))) := by
    funext w
    simp only [collectSeedList,Fin.cons_zero,Fin.cons_succ,collectSeedTailProgram]
  rw [he] at hs
  exact hs.trans (seededOutputLaw_bind_of_usesAtMost μ η
    (Measure.pi (fun _ : Fin is.length => η)) q₀ y₀ o₀ (fun _ => o₀) a₀ reply hr
    (p i) (hp i) (cost i) (hcost i) (collectSeedTailProgram o₀ p i is)
    (collectSeedTailProgram_measurable q₀ o₀ p hp i is) ((is.map cost).sum)
    (collectSeedTailProgram_usesAtMost o₀ p cost hcost i is))

/-- Equality of the individual seeded output laws implies equality of the
whole ordered packet, with independent seeds for the separate entries. -/
theorem collectSeedList_outputLaw_congr (μ : Measure Ω) (η : Measure S) (θ : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] [IsProbabilityMeasure θ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : I → S → OracleProgram Q Y O) (hp : ∀ i, MeasurableFamily q₀ o₀ (p i))
    (p' : I → T → OracleProgram Q Y O) (hp' : ∀ i, MeasurableFamily q₀ o₀ (p' i))
    (cost : I → ℕ) (hcost : ∀ i s, UsesAtMost (cost i) (p i s))
    (hcost' : ∀ i t, UsesAtMost (cost i) (p' i t))
    (hlaw : ∀ i, seededOutputLaw μ η q₀ o₀ reply (p i) (cost i)=
      seededOutputLaw μ θ q₀ o₀ reply (p' i) (cost i)) (is : List I) :
    seededOutputLaw μ (Measure.pi (fun _ : Fin is.length => η)) q₀ (fun _ => o₀) reply
      (collectSeedList o₀ p is) ((is.map cost).sum)=
      seededOutputLaw μ (Measure.pi (fun _ : Fin is.length => θ)) q₀ (fun _ => o₀) reply
        (collectSeedList o₀ p' is) ((is.map cost).sum) := by
  induction is with
  | nil => simp only [collectSeedList,List.map_nil,List.sum_nil,seededOutputLaw_done]
  | cons i is ih =>
    rw [collectSeedList_outputLaw_cons μ η q₀ y₀ o₀ a₀ reply hr p hp cost hcost i is,
      collectSeedList_outputLaw_cons μ θ q₀ y₀ o₀ a₀ reply hr p' hp' cost hcost' i is,hlaw i]
    apply congrArg (fun k : O → Measure (I → O) =>
      (seededOutputLaw μ θ q₀ o₀ reply (p' i) (cost i)).bind k)
    funext o
    rw [collectSeedTailProgram_kernel μ η q₀ y₀ o₀ a₀ reply hr p hp cost hcost i is o,
      collectSeedTailProgram_kernel μ θ q₀ y₀ o₀ a₀ reply hr p' hp' cost hcost' i is o,ih]

end
end OracleProgram
end SecondOrder
