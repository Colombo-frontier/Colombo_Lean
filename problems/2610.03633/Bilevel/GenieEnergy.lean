import Bilevel.GenieProtocol
import Bilevel.ProjectionQuery
import Bilevel.ProjectionTraceBudget

/-! Every intermediate unrevealed-column energy is controlled on the actual good event. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.GenieProtocol
open EuclideanGaussian ProjectionPosterior ProjectionGeometry ProjectionTrace ProjectionEnergy

def Known {d T : ℕ} (V : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T) : Prop :=
  ∀ i ∈ S, U i ∈ V

def BoundedEnergy {d T : ℕ} (V : Submodule ℝ (Space d)) (S : Set (Fin T))
    (U : Frame d T) (e : ℝ) : Prop := ∀ i, i ∉ S → energy V (U i) ≤ e

def Safe {d T : ℕ} (cap : ℝ) : {m r : ℕ} → Protocol d T m r →
    Submodule ℝ (Space d) → Set (Fin T) → Frame d T → Prop
  | _, _, .halt, V, S, U => BoundedEnergy V S U cap
  | _, _, .query w next, V, S, U => BoundedEnergy V S U cap ∧
      Safe cap (next (queryObservation d T w U)) (V ⊔ Submodule.span ℝ {w}) S U
  | _, _, .reveal i next, V, S, U => BoundedEnergy V S U cap ∧
      Safe cap (next (U i)) (V ⊔ Submodule.span ℝ {U i}) (insert i S) U

theorem reveal_energy {d T : ℕ} (V : Submodule ℝ (Space d)) (S : Set (Fin T))
    (U : Frame d T) (hU : Orthonormal ℝ U) (e : ℝ) (he : 0 ≤ e) (he1 : e < 1)
    (hknown : Known V S U) (henergy : BoundedEnergy V S U e) (j : Fin T) :
    BoundedEnergy (V ⊔ Submodule.span ℝ {U j}) (insert j S) U (e/(1-e)) := by
  intro i hi
  have hiS : i ∉ S := fun h => hi (Set.mem_insert_of_mem _ h)
  have hij : i ≠ j := fun h => hi (h ▸ Set.mem_insert _ _)
  have hei := henergy i hiS
  by_cases hj : j ∈ S
  · have hspan : Submodule.span ℝ {U j} ≤ V := Submodule.span_le.mpr (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hknown j hj)
    rw [sup_eq_left.mpr hspan]
    apply hei.trans
    apply (le_div_iff₀ (by linarith : 0 < 1-e)).mpr
    nlinarith [sq_nonneg e]
  · have hej := henergy j hj
    have hj1 : energy V (U j) < 1 := hej.trans_lt he1
    have hgeom := projection_revelation_bound V (U i) (U j) (hU.norm_eq_one j) hj1 (hU.inner_eq_zero hij)
    apply hgeom.trans
    apply (div_le_div_iff₀ (by linarith : 0 < 1-energy V (U j)) (by linarith : 0 < 1-e)).mpr
    have h₁ := mul_nonneg (show 0 ≤ e-energy V (U i) by linarith) (show 0 ≤ 1-e by linarith)
    have h₂ := mul_nonneg he (show 0 ≤ e-energy V (U j) by linarith)
    nlinarith

theorem safe_of_good {d T : ℕ} (b : ℝ) (hb : 0 ≤ b) (M R : ℕ)
    (hcap : (R : ℝ)*((M : ℝ)*b) < 1) {m r : ℕ} (P : Protocol d T m r) :
    ∀ (V : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T),
      Orthonormal ℝ U → Valid P V → ¬ bad b P U → Known V S U →
      ∀ (q s : ℕ) (e : ℝ), q+m ≤ M → s+r ≤ R → Trace b q s e → BoundedEnergy V S U e →
      Safe (envelope ((M : ℝ)*b) R) P V S U := by
  induction P with
  | halt =>
    intro V S U _ _ _ _ q s e hq hs htr hE
    intro i hi
    exact (hE i hi).trans (bounded_counts hb htr (by omega) (by omega) hcap)
  | @query m r w next ih =>
    intro V S U hU hV hgood hknown q s e hq hs htr hE
    have hhead : ∀ i : Fin T, ⟪w,U i⟫ ^ 2 ≤ b := by
      intro i
      exact (lt_of_not_ge (fun h => hgood (Or.inl ⟨i,h⟩))).le
    have hnext : ¬ bad b (next (queryObservation d T w U)) U := fun h => hgood (Or.inr h)
    refine ⟨fun i hi => (hE i hi).trans (bounded_counts hb htr (by omega) (by omega) hcap), ?_⟩
    refine ih (queryObservation d T w U) _ S U hU (hV.2.2 _) hnext ?_
      (q+1) s (e+b) (by omega) hs (Trace.query htr (add_nonneg (nonneg htr) hb) le_rfl) ?_
    · intro i hi
      exact (show V ≤ V ⊔ Submodule.span ℝ {w} from le_sup_left) (hknown i hi)
    · intro i hi
      have hinner : ⟪U i,w⟫ ^ 2 ≤ b := by rw [real_inner_comm]; exact hhead i
      exact (ProjectionQuery.query_energy_le V w (U i) hV.1 hV.2.1 b hinner).trans
        (add_le_add_right (hE i hi) b)
  | @reveal m r j next ih =>
    intro V S U hU hV hgood hknown q s e hq hs htr hE
    have he1 : e < 1 := before_next_reveal hb htr (by omega) (by omega) hcap
    refine ⟨fun i hi => (hE i hi).trans (bounded_counts hb htr (by omega) (by omega) hcap), ?_⟩
    refine ih (U j) _ (insert j S) U hU (hV _) hgood ?_ q (s+1) (e/(1-e)) hq (by omega)
      (Trace.reveal htr (div_nonneg (nonneg htr) (by linarith)) le_rfl) ?_
    · intro i hi
      rcases Set.mem_insert_iff.mp hi with rfl | hi
      · exact (show Submodule.span ℝ {U i} ≤ V ⊔ Submodule.span ℝ {U i} from le_sup_right)
          (Submodule.mem_span_singleton_self _)
      · exact (show V ≤ V ⊔ Submodule.span ℝ {U j} from le_sup_left) (hknown i hi)
    · exact reveal_energy V S U hU e (nonneg htr) he1 hknown hE j

theorem initial_safe {d T M R : ℕ} (b : ℝ) (hb : 0 ≤ b)
    (hcap : (R : ℝ)*((M : ℝ)*b) < 1) (P : Protocol d T M R)
    (hV : Valid P ⊥) (U : Frame d T) (hU : Orthonormal ℝ U) (hgood : ¬ bad b P U) :
    Safe (envelope ((M : ℝ)*b) R) P ⊥ ∅ U := by
  apply safe_of_good b hb M R hcap P ⊥ ∅ U hU hV hgood
    (fun _ h => False.elim h) 0 0 0 (by omega) (by omega) Trace.initial
  intro i _
  simp [energy,project]

end Bilevel.GenieProtocol
