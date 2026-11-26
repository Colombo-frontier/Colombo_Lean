import SecondOrder.DrawsLawTransport
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory
open scoped BigOperators

namespace SecondOrder
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω]

theorem drawsVector_box (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (s : Fin n → Set Ω) :
    drawsLaw μ n ((drawsVector id n) ⁻¹' Set.pi Set.univ s)=∏ i, μ (s i) := by
  induction n with
  | zero => simp [drawsLaw,drawsVector]
  | succ n ih =>
    have he : (drawsVector id (n+1)) ⁻¹' Set.pi Set.univ s=
        ((drawsVector id n) ⁻¹' Set.pi Set.univ (fun i => s i.castSucc)) ×ˢ s (Fin.last n) := by
      ext w
      rcases w with ⟨u,z⟩
      change (∀ i : Fin (n+1), i∈Set.univ → drawsVector id (n+1) (u,z) i∈s i) ↔
        ((∀ i : Fin n, i∈Set.univ → drawsVector id n u i∈s i.castSucc) ∧ z∈s (Fin.last n))
      simp [Set.mem_pi,Fin.forall_iff_castSucc,drawsVector,and_comm]
    rw [he]
    change ((drawsLaw μ n).prod μ) (_ ×ˢ _) = _
    rw [Measure.prod_prod,ih,Fin.prod_univ_castSucc]

theorem drawsVector_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (drawsVector id n) (drawsLaw μ n) (Measure.pi (fun _ : Fin n => μ)) := by
  refine ⟨drawsVector_measurable measurable_id n,?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (drawsVector_measurable measurable_id n) (MeasurableSet.univ_pi hs)]
  exact drawsVector_box μ n s

def vectorDraws {Ω : Type} : (n : ℕ) → (Fin n → Ω) → Draws Ω n
  | 0, _ => PUnit.unit
  | n+1, w => (vectorDraws n (fun i => w i.castSucc),w (Fin.last n))

theorem vectorDraws_measurable (n : ℕ) : Measurable (@vectorDraws Ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp (measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc))).prodMk
      (measurable_pi_apply (Fin.last n))

omit [MeasurableSpace Ω] in
theorem drawsVector_vectorDraws (n : ℕ) (w : Fin n → Ω) : drawsVector id n (vectorDraws n w)=w := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [vectorDraws,drawsVector,Fin.snoc_last,id_eq]
    · simp only [vectorDraws,drawsVector,Fin.snoc_castSucc,ih]

omit [MeasurableSpace Ω] in
theorem vectorDraws_drawsVector (n : ℕ) (w : Draws Ω n) : vectorDraws n (drawsVector id n w)=w := by
  induction n with
  | zero => exact Subsingleton.elim (α := PUnit) _ _
  | succ n ih =>
    simp only [vectorDraws,drawsVector,Fin.snoc_last,Fin.snoc_castSucc,id_eq,ih,Prod.mk.eta]

theorem vectorDraws_measurePreserving (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (vectorDraws n) (Measure.pi (fun _ : Fin n => μ)) (drawsLaw μ n) := by
  refine ⟨vectorDraws_measurable n,?_⟩
  rw [←(drawsVector_measurePreserving μ n).map_eq,
    Measure.map_map (vectorDraws_measurable n) (drawsVector_measurable measurable_id n)]
  have he : @vectorDraws Ω n ∘ drawsVector id n=id := by funext w; exact vectorDraws_drawsVector n w
  rw [he,Measure.map_id]

/-- Enumeration order is immaterial for independent identically distributed
samples. This applies to the actual finite slot enumeration used by queries. -/
theorem pi_reindex_measurePreserving {I J : Type} [Fintype I] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (e : I ≃ J) :
    MeasurePreserving (fun w : I → Ω => fun j => w (e.symm j))
      (Measure.pi (fun _ : I => μ)) (Measure.pi (fun _ : J => μ)) := by
  convert measurePreserving_piCongrLeft (fun _ : J => μ) e using 1
  funext w j
  simpa only [Equiv.apply_symm_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : J => Ω) e w (e.symm j)).symm

theorem pi_uncurry_measurePreserving {I J : Type} [Fintype I] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun w : I → J → Ω => fun p : I × J => w p.1 p.2)
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => μ)))
      (Measure.pi (fun _ : I × J => μ)) := by
  have hm : Measurable (fun w : I → J → Ω => fun p : I × J => w p.1 p.2) :=
    measurable_pi_lambda _ (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
  refine ⟨hm,?_⟩
  apply Eq.symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun w : I → J → Ω => fun p : I × J => w p.1 p.2) ⁻¹' Set.pi Set.univ s=
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s (i,j))) := by
    ext w
    simp [Set.mem_pi]
  rw [he,Measure.pi_pi]
  simp only [Measure.pi_pi,Fintype.prod_prod_type]

end
end SecondOrder
