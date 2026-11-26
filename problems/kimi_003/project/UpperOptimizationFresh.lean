import UpperOptimization

/-! Genuine fresh-round independence on a finite iid product space. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace Task006.Full

theorem finite_past_indep_current {T : ℕ} {B E : Type*}
    [MeasurableSpace B] [MeasurableSpace E] (ν : Measure B) [IsProbabilityMeasure ν]
    (t : Fin T) (X : (Fin T → B) → E) (hX : Measurable X)
    (hpast : ∀ w w', (∀ j : Fin T, j.val < t.val → w j = w' j) → X w = X w') :
    IndepFun X (fun w : Fin T → B => w t) (Measure.pi (fun _ : Fin T => ν)) := by
  classical
  let b₀ : B := Classical.choice (nonempty_of_isProbabilityMeasure ν)
  let S : Finset (Fin T) := Finset.univ.filter (fun j => j.val < t.val)
  let fill : (S → B) → (Fin T → B) := fun h j => if hj : j ∈ S then h ⟨j, hj⟩ else b₀
  have hfill : Measurable fill := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j ∈ S
    · simpa only [fill, dif_pos hj] using measurable_pi_apply (⟨j, hj⟩ : S)
    · simpa only [fill, dif_neg hj] using (measurable_const : Measurable (fun _ : S → B => b₀))
  let φ : (S → B) → E := X ∘ fill
  have hφ : Measurable φ := hX.comp hfill
  have heq : (fun w : Fin T → B => φ (fun j : S => w j.val)) = X := by
    funext w
    apply hpast
    intro j hj
    have hjS : j ∈ S := by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hj
    simp only [φ, Function.comp_apply, fill, dif_pos hjS]
  have hind : iIndepFun (fun j : Fin T => fun w : Fin T → B => w j)
      (Measure.pi (fun _ : Fin T => ν)) :=
    iIndepFun_pi (X := fun _ b => b) (fun _ => aemeasurable_id)
  have hdisj : Disjoint S ({t} : Finset (Fin T)) := by simp [S]
  have hpair := (hind.indepFun_finset S {t} hdisj (fun _ => measurable_pi_apply _)).comp
    hφ (measurable_pi_apply (⟨t, Finset.mem_singleton_self t⟩ : ({t} : Finset (Fin T))))
  change IndepFun (fun w : Fin T → B => φ (fun j : S => w j.val)) (fun w => w t)
    (Measure.pi (fun _ : Fin T => ν)) at hpair
  rw [heq] at hpair
  exact hpair

/-- Fubini for a fresh block at a random past-dependent state. The product law
is derived from finite-product independence, rather than assumed as a sampling
contract. -/
theorem fresh_block_integral {T : ℕ} {B E : Type*}
    [MeasurableSpace B] [MeasurableSpace E] (ν : Measure B) [IsProbabilityMeasure ν]
    (t : Fin T) (X : (Fin T → B) → E) (hX : Measurable X)
    (hpast : ∀ w w', (∀ j : Fin T, j.val < t.val → w j = w' j) → X w = X w')
    (H : E × B → ℝ) (hH : Measurable H)
    (hHi : Integrable H (((Measure.pi (fun _ : Fin T => ν)).map X).prod ν)) :
    (∫ w, H (X w, w t) ∂Measure.pi (fun _ : Fin T => ν)) =
      ∫ x, (∫ b, H (x, b) ∂ν) ∂((Measure.pi (fun _ : Fin T => ν)).map X) := by
  have hind := finite_past_indep_current ν t X hX hpast
  have hmap := hind.map_prod_eq_prod_map_map hX.aemeasurable (measurable_pi_apply t).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin T => ν) t).map_eq] at hmap
  calc
    (∫ w, H (X w, w t) ∂Measure.pi (fun _ : Fin T => ν)) =
        ∫ p, H p ∂((Measure.pi (fun _ : Fin T => ν)).map (fun w => (X w, w t))) :=
      (integral_map (hX.prodMk (measurable_pi_apply t)).aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ p, H p ∂(((Measure.pi (fun _ : Fin T => ν)).map X).prod ν) := by rw [hmap]
    _ = _ := integral_prod H hHi

#print axioms finite_past_indep_current
#print axioms fresh_block_integral

end Task006.Full
