import SecondOrder.DependentSelectorJets
import SecondOrder.CurvatureFrontierFormula

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {T : ℕ} {E : Fin (T+1) → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

/-- The general adjacent population chain, including a public regularizer. -/
def conservativePopulation (reg : PiLp 2 E → ℝ)
    (W p : (i : Fin (T+1)) → E i → ℝ) (x : PiLp 2 E) : ℝ :=
  reg x+W 0 (x 0)+∑ i : Fin T, 2*(p i.castSucc (x i.castSucc)*W i.succ (x i.succ))

/-- The terminal payload is zero. All gates, including the terminal gate,
remain in the full reverse selector. -/
def conservativePayload (W S : (i : Fin (T+1)) → E i → ℝ) (j : ℕ) (x : PiLp 2 E) : ℝ :=
  if hj : j<T+1 then curvaturePayloadScale j*(S ⟨j,hj⟩ (x ⟨j,hj⟩)-W ⟨j,hj⟩ (x ⟨j,hj⟩)) else 0

/-- A single scalar loss with all selector-weight derivatives retained. -/
def conservativeChain (reg : PiLp 2 E → ℝ)
    (W S p : (i : Fin (T+1)) → E i → ℝ) (x : PiLp 2 E) : ℝ :=
  conservativePopulation reg W p x+dependentReverseSelector p (conservativePayload W S) x

def conservativeTruncatedChain (reg : PiLp 2 E → ℝ)
    (W S p : (i : Fin (T+1)) → E i → ℝ) (k : ℕ) : PiLp 2 E → ℝ :=
  conservativeChain reg W S (dependentPrefixGates p k)

theorem conservativePopulation_contDiff (reg : PiLp 2 E → ℝ)
    (W p : (i : Fin (T+1)) → E i → ℝ) {r : WithTop ℕ∞}
    (hreg : ContDiff ℝ r reg) (hW : ∀ i, ContDiff ℝ r (W i)) (hp : ∀ i, ContDiff ℝ r (p i)) :
    ContDiff ℝ r (conservativePopulation reg W p) := by
  apply ContDiff.add
  · exact hreg.add ((hW 0).comp (dependentBlockProj (E := E) (0 : Fin (T+1))).contDiff)
  · apply ContDiff.sum
    intro i _
    exact contDiff_const.mul (((hp i.castSucc).comp (dependentBlockProj (E := E) i.castSucc).contDiff).mul
      ((hW i.succ).comp (dependentBlockProj (E := E) i.succ).contDiff))

theorem conservativePayload_contDiff (W S : (i : Fin (T+1)) → E i → ℝ)
    {r : WithTop ℕ∞} (hW : ∀ i, ContDiff ℝ r (W i)) (hS : ∀ i, ContDiff ℝ r (S i)) (j : ℕ) :
    ContDiff ℝ r (conservativePayload W S j) := by
  by_cases hj : j<T+1
  · change ContDiff ℝ r (fun x => if _ : j<T+1 then _ else _)
    simp only [dif_pos hj]
    exact contDiff_const.mul (((hS ⟨j,hj⟩).sub (hW ⟨j,hj⟩)).comp
      (dependentBlockProj (E := E) (⟨j,hj⟩ : Fin (T+1))).contDiff)
  · have he : conservativePayload W S j = fun _ => (0:ℝ) := by
      funext x
      simp only [conservativePayload,dif_neg hj]
    rw [he]
    exact contDiff_const

theorem conservativeChain_contDiff (reg : PiLp 2 E → ℝ)
    (W S p : (i : Fin (T+1)) → E i → ℝ) {r : WithTop ℕ∞}
    (hreg : ContDiff ℝ r reg) (hW : ∀ i, ContDiff ℝ r (W i))
    (hS : ∀ i, ContDiff ℝ r (S i)) (hp : ∀ i, ContDiff ℝ r (p i)) :
    ContDiff ℝ r (conservativeChain reg W S p) :=
  (conservativePopulation_contDiff reg W p hreg hW hp).add
    (dependentReverseSelector_contDiff p _ hp (fun j _ => conservativePayload_contDiff W S hW hS j))

theorem conservativeTruncatedChain_contDiff (reg : PiLp 2 E → ℝ)
    (W S p : (i : Fin (T+1)) → E i → ℝ) {r : WithTop ℕ∞}
    (hreg : ContDiff ℝ r reg) (hW : ∀ i, ContDiff ℝ r (W i))
    (hS : ∀ i, ContDiff ℝ r (S i)) (hp : ∀ i, ContDiff ℝ r (p i)) (k : ℕ) :
    ContDiff ℝ r (conservativeTruncatedChain reg W S p k) :=
  conservativeChain_contDiff reg W S _ hreg hW hS (dependentPrefixGates_contDiff p k hp)

theorem conservativePopulation_jetEq (reg : PiLp 2 E → ℝ)
    (W : (i : Fin (T+1)) → E i → ℝ) {p q : (i : Fin (T+1)) → E i → ℝ}
    (hreg : ContDiff ℝ 2 reg) (hW : ∀ i, ContDiff ℝ 2 (W i)) (x : PiLp 2 E)
    (hp : ∀ i, ScalarJetEq (p i) (q i) (x i)) :
    ScalarJetEq (conservativePopulation reg W p) (conservativePopulation reg W q) x := by
  apply ScalarJetEq.add
  · exact (ScalarJetEq.refl hreg x).add (ScalarJetEq.refl
      ((hW 0).comp (dependentBlockProj (E := E) (0 : Fin (T+1))).contDiff) x)
  · apply ScalarJetEq.sum
    intro i _
    exact (((hp i.castSucc).comp_linear (dependentBlockProj (E := E) i.castSucc)).mul
      (ScalarJetEq.refl ((hW i.succ).comp (dependentBlockProj (E := E) i.succ).contDiff) x)).const_mul 2

/-- Zero future gates with flat first and second derivatives may be replaced
by zero functions in the entire scalar loss, including all noise weights. -/
theorem conservativeChain_truncate_jet (reg : PiLp 2 E → ℝ)
    (W S p : (i : Fin (T+1)) → E i → ℝ)
    (hreg : ContDiff ℝ 2 reg) (hW : ∀ i, ContDiff ℝ 2 (W i))
    (hS : ∀ i, ContDiff ℝ 2 (S i)) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (hflat : ∀ i y, p i y=0 → gradient (p i) y=0 ∧ fderiv ℝ (gradient (p i)) y=0)
    (k : ℕ) (x : PiLp 2 E) (hfuture : ∀ i, k ≤ i.val → p i (x i)=0) :
    ScalarJetEq (conservativeChain reg W S p) (conservativeTruncatedChain reg W S p k) x := by
  have hgate : ∀ i, ScalarJetEq (p i) (dependentPrefixGates p k i) (x i) :=
    dependentPrefixGates_jetEq p k hp x (fun i hi => scalarJetEq_zero_of_flat (hp i) (x i)
      (hfuture i hi) (hflat i (x i) (hfuture i hi)).1 (hflat i (x i) (hfuture i hi)).2)
  exact (conservativePopulation_jetEq reg W hreg hW x hgate).add
    (dependentReverseSelector_jetEq hgate (fun j _ => ScalarJetEq.refl
      (conservativePayload_contDiff W S hW hS j) x))

end
end SecondOrder
