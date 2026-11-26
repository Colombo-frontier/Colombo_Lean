import ReadOnceIndependence
import OracleSemantics
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory

namespace Task006.Full

abbrev OffHandle (h : ℕ) := {k : ℕ // k ≠ h}

def offTape {Ω : Type*} (h : ℕ) (tape : ℕ → Ω) : OffHandle h → Ω := fun k => tape k.val

def restoreTape {Ω : Type*} (h : ℕ) (z : Ω) (tape : OffHandle h → Ω) : ℕ → Ω :=
  fun k => if hk : k = h then z else tape ⟨k,hk⟩

lemma measurable_offTape {Ω : Type*} [MeasurableSpace Ω] (h : ℕ) :
    Measurable (offTape (Ω := Ω) h) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

lemma measurable_restoreTape {Ω : Type*} [MeasurableSpace Ω] (h : ℕ) (z : Ω) :
    Measurable (restoreTape h z) := by
  apply measurable_pi_lambda
  intro k
  by_cases hk : k = h
  · simpa only [restoreTape, dif_pos hk] using (measurable_const : Measurable (fun _ : OffHandle h → Ω => z))
  · simpa only [restoreTape, dif_neg hk] using (measurable_pi_apply (⟨k,hk⟩ : OffHandle h))

lemma restore_offTape {Ω : Type*} (h : ℕ) (z : Ω) (tape : ℕ → Ω) :
    restoreTape h z (offTape h tape) = Function.update tape h z := by
  funext k
  by_cases hk : k = h
  · subst k; simp [restoreTape]
  · simp [restoreTape, hk, offTape, Function.update_of_ne hk]

/-- A coordinate is independent of the entire collection of all other coordinates. -/
theorem iid_coordinate_indep_offTape {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℕ) :
    IndepFun (fun tape : ℕ → Ω => tape h) (offTape h) (iidHandleLaw μ) := by
  let hi := iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ x => x)
    (fun _ => measurable_id)
  change IndepFun (fun tape : ℕ → Ω => tape h)
    (fun tape (k : OffHandle h) => tape k.val) (iidHandleLaw μ)
  apply IndepFun.indepFun_process
    (Y := fun k : OffHandle h => fun tape : ℕ → Ω => tape k.val)
    (P := iidHandleLaw μ) (measurable_pi_apply h)
    (fun k => measurable_pi_apply k.val)
  intro I
  let T : Finset ℕ := I.image Subtype.val
  have hd : Disjoint ({h} : Finset ℕ) T := by
    apply Finset.disjoint_left.mpr
    intro k hk ht
    have ekh : k = h := by simpa using hk
    subst k
    rcases Finset.mem_image.mp ht with ⟨j,hj,he⟩
    exact j.property he
  have hfin := hi.indepFun_finset {h} T hd (fun _ => measurable_pi_apply _)
  let f : ((k : ({h} : Finset ℕ)) → Ω) → Ω := fun x => x ⟨h,by simp⟩
  let g : ((k : T) → Ω) → ((j : I) → Ω) :=
    fun x j => x ⟨j.val.val, Finset.mem_image.mpr ⟨j.val,j.property,rfl⟩⟩
  have hf : Measurable f := measurable_pi_apply _
  have hg : Measurable g := by exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  simpa only [f,g,Function.comp_def,offTape,iidHandleLaw] using hfin.comp hf hg

end Task006.Full
