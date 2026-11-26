import SecondOrder.SeededCollectionLaw
import SecondOrder.FinitePacketSeeds

open MeasureTheory
open scoped Classical

namespace SecondOrder
namespace OracleProgram
noncomputable section

variable {I Q Y O Ω S T : Type} [MeasurableSpace Q] [MeasurableSpace Y]
  [MeasurableSpace O] [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]

theorem collectList_seededOutputLaw_finite (μ : Measure Ω) (η : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : I → S → OracleProgram Q Y O) (hp : ∀ i, MeasurableFamily q₀ o₀ (p i))
    (is : List I) (hi : is.Nodup) (N : ℕ) :
    seededOutputLaw μ (Measure.infinitePi (fun _ : I => η)) q₀ (fun _ => o₀) reply
      (fun seeds => collectList o₀ (fun i => p i (seeds i)) is) N=
      seededOutputLaw μ (Measure.pi (fun _ : Fin is.length => η)) q₀ (fun _ => o₀) reply
        (collectSeedList o₀ p is) N := by
  have ht := infinitePi_list_measurePreserving η is hi
  have hs := seededOutputLaw_mapSeed μ (Measure.infinitePi (fun _ : I => η)) q₀ y₀
    (fun _ => o₀) a₀ reply hr (collectSeedList o₀ p is)
    (collectSeedList_measurable q₀ o₀ p hp is)
    (fun seeds : I → S => fun j : Fin is.length => seeds (is.get j)) ht.measurable N
  rw [ht.map_eq] at hs
  have he : (fun seeds : I → S => collectSeedList o₀ p is (fun j => seeds (is.get j)))=
      (fun seeds : I → S => collectList o₀ (fun i => p i (seeds i)) is) := by
    funext seeds
    exact collectSeedList_eq_collectList o₀ p is seeds
  rw [he] at hs
  exact hs.symm

theorem collectSeedReplies_map_infinitePi (θ : Measure T) [IsProbabilityMeasure θ]
    (o₀ : O) (g : I → T → O) (hg : ∀ i, Measurable (g i)) (is : List I) (hi : is.Nodup) :
    Measure.map (fun seeds : I → T => fun i => if i∈is then g i (seeds i) else o₀)
      (Measure.infinitePi (fun _ : I => θ))=
      Measure.map (collectSeedReplies o₀ g is) (Measure.pi (fun _ : Fin is.length => θ)) := by
  have ht := infinitePi_list_measurePreserving θ is hi
  rw [←ht.map_eq,Measure.map_map (collectSeedReplies_measurable o₀ g hg is) ht.measurable]
  apply congrArg (fun k : (I → T) → I → O => Measure.map k (Measure.infinitePi (fun _ : I => θ)))
  funext seeds
  exact (collectSeedReplies_list o₀ g is seeds).symm

/-- A finite packet of reply programs has the same joint law as independent
local estimators whenever each individual estimator has the right law. -/
theorem collectList_seededOutputLaw_samples (μ : Measure Ω) (η : Measure S) (θ : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] [IsProbabilityMeasure θ]
    (q₀ : Q) (y₀ : Y) (o₀ : O) (a₀ : Ω) (reply : Q → Ω → Y)
    (hr : Measurable (fun w : Q × Ω => reply w.1 w.2))
    (p : I → S → OracleProgram Q Y O) (hp : ∀ i, MeasurableFamily q₀ o₀ (p i))
    (cost : I → ℕ) (hcost : ∀ i s, UsesAtMost (cost i) (p i s))
    (g : I → T → O) (hg : ∀ i, Measurable (g i))
    (hlaw : ∀ i, seededOutputLaw μ η q₀ o₀ reply (p i) (cost i)=Measure.map (g i) θ)
    (is : List I) (hi : is.Nodup) :
    seededOutputLaw μ (Measure.infinitePi (fun _ : I => η)) q₀ (fun _ => o₀) reply
      (fun seeds => collectList o₀ (fun i => p i (seeds i)) is) ((is.map cost).sum)=
      Measure.map (fun seeds : I → T => fun i => if i∈is then g i (seeds i) else o₀)
        (Measure.infinitePi (fun _ : I => θ)) := by
  rw [collectList_seededOutputLaw_finite μ η q₀ y₀ o₀ a₀ reply hr p hp is hi,
    collectSeedReplies_map_infinitePi θ o₀ g hg is hi]
  have hpd : ∀ i, MeasurableFamily q₀ o₀ (fun t => (OracleProgram.done (g i t) : OracleProgram Q Y O)) :=
    fun i => measurableFamily_done q₀ o₀ _ (hg i)
  have hc : ∀ i t, UsesAtMost (cost i) (OracleProgram.done (g i t) : OracleProgram Q Y O) :=
    fun i _ => by cases cost i <;> trivial
  have hl : ∀ i, seededOutputLaw μ η q₀ o₀ reply (p i) (cost i)=
      seededOutputLaw μ θ q₀ o₀ reply (fun t => .done (g i t)) (cost i) := by
    intro i
    rw [seededOutputLaw_done_family μ θ q₀ o₀ reply (g i) (hg i) (cost i)]
    exact hlaw i
  rw [collectSeedList_outputLaw_congr μ η θ q₀ y₀ o₀ a₀ reply hr p hp
    (fun i t => .done (g i t)) hpd cost hcost hc hl is]
  have he : collectSeedList (Q := Q) (Y := Y) o₀ (fun i t => .done (g i t)) is=
      (fun seeds => .done (collectSeedReplies o₀ g is seeds)) := by
    funext seeds
    exact collectSeedList_done o₀ g is seeds
  rw [he,seededOutputLaw_done_family μ _ q₀ (fun _ => o₀) reply _
    (collectSeedReplies_measurable o₀ g hg is)]

end
end OracleProgram
end SecondOrder
