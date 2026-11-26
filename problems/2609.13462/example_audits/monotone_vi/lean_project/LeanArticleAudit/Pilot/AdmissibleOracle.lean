import LeanArticleAudit.Pilot.UpperInterfaces

/-!
# Exact symmetric jets from finite admissible regularity

The admissible class assumes only `C^(p - 1)` regularity on a neighbourhood
of the feasible domain.  This file proves directly that every derivative of
order `j < p` is symmetric.  In particular, it does not use mathlib's
`ContDiffAt.domDomCongr_iteratedFDeriv`, whose hypothesis is `C^∞`.
-/

open Set Filter Topology

namespace LeanArticleAudit.Pilot

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uncurrying two derivatives after an `n`th derivative gives exactly the
`(n + 2)`nd iterated Fréchet derivative, with the first two variables in the
two newly differentiated slots. -/
private lemma iteratedFDeriv_add_two_apply {f : E → F} {x : E} {n : ℕ}
    (v₀ v₁ : E) (tail : Fin n → E) :
    iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ n f) x ![v₀, v₁] tail =
      iteratedFDeriv ℝ (n + 2) f x (Fin.cases v₀ (Fin.cases v₁ tail)) := by
  simp only [iteratedFDeriv_two_apply]
  rw [show fderiv ℝ (iteratedFDeriv ℝ n f) =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F) ∘
        iteratedFDeriv ℝ (n + 1) f from fderiv_iteratedFDeriv]
  rw [LinearIsometryEquiv.comp_fderiv]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.comp_apply]
  rfl

/-- Removing the first coordinate intertwines corresponding adjacent swaps. -/
private lemma tail_adjacent_swap {E₀ : Type*} {n : ℕ}
    (k : Fin n) (v : Fin (n + 2) → E₀) :
    Fin.tail (fun q => v (Equiv.swap k.succ.castSucc k.succ.succ q)) =
      fun q => Fin.tail v (Equiv.swap k.castSucc k.succ q) := by
  funext q
  change v (Equiv.swap k.succ.castSucc k.succ.succ q.succ) =
    v ((Equiv.swap k.castSucc k.succ q).succ)
  congr 1
  apply Fin.ext
  simp only [Fin.val_succ, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- Finite `C^n` regularity suffices for symmetry of the `n`th iterated
Fréchet derivative over `ℝ`.

The induction proves invariance under adjacent swaps.  The first adjacent
swap is Schwarz symmetry for `D^n f`; the remaining swaps follow by
differentiating the induction hypothesis on a neighbourhood.  Adjacent swaps
then generate the whole finite symmetric group. -/
theorem finiteContDiffAt_iteratedFDeriv_symmetric {n : ℕ} {f : E → F} {x : E}
    (h : ContDiffAt ℝ n f x) (σ : Equiv.Perm (Fin n)) :
    ContinuousMultilinearMap.domDomCongr σ (iteratedFDeriv ℝ n f x) =
      iteratedFDeriv ℝ n f x := by
  induction n using Nat.twoStepInduction generalizing f x with
  | zero =>
      have hσ : σ = 1 := Subsingleton.elim _ _
      subst σ
      ext v
      simp [ContinuousMultilinearMap.domDomCongr_apply]
  | one =>
      have hσ : σ = 1 := Subsingleton.elim _ _
      subst σ
      ext v
      simp [ContinuousMultilinearMap.domDomCongr_apply]
  | more n ih ih' =>
      let A := iteratedFDeriv ℝ (n + 2) f x
      have hfront : ContinuousMultilinearMap.domDomCongr
          (Equiv.swap (0 : Fin (n + 2)) (Fin.succ 0)) A = A := by
        have hDn : ContDiffAt ℝ 2 (iteratedFDeriv ℝ n f) x :=
          h.iteratedFDeriv_right (by simp [add_comm])
        have hs := hDn.isSymmSndFDerivAt (by simp)
        ext w
        simp only [A, ContinuousMultilinearMap.domDomCongr_apply]
        calc
          iteratedFDeriv ℝ (n + 2) f x
              (fun i => w (Equiv.swap 0 (Fin.succ 0) i)) =
              iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ n f) x
                ![w (Fin.succ 0), w 0] (fun i => w i.succ.succ) := by
            rw [iteratedFDeriv_add_two_apply]
            congr 1
            funext i
            refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
            · rw [Equiv.swap_apply_left]
              rfl
            · rw [Equiv.swap_apply_right]
              change w 0 = Fin.cases (w (Fin.succ 0))
                (fun i => Fin.cases (w 0) (fun i => w i.succ.succ) i) (Fin.succ 0)
              rfl
            · rw [Equiv.swap_apply_of_ne_of_ne]
              · rfl
              · exact Fin.succ_ne_zero _
              · intro heq
                have hh : i.succ = (0 : Fin (n + 1)) := Fin.succ_injective _ heq
                exact Fin.succ_ne_zero _ hh
          _ = iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ n f) x
                ![w 0, w 1] (fun i => w i.succ.succ) := by
            rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
            simpa using congrArg (fun L => L (fun i => w i.succ.succ))
              (hs (w (Fin.succ 0)) (w 0))
          _ = iteratedFDeriv ℝ (n + 2) f x w := by
            rw [iteratedFDeriv_add_two_apply]
            congr 1
            funext i
            refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
            · rfl
            · change Fin.cases (w 0)
                (fun i => Fin.cases (w (Fin.succ 0)) (fun i => w i.succ.succ) i)
                  (Fin.succ 0) = w (Fin.succ 0)
              rfl
            · simp
      have htail (k : Fin n) : ContinuousMultilinearMap.domDomCongr
          (Equiv.swap k.succ.castSucc k.succ.succ) A = A := by
        have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) x :=
          h.differentiableAt_iteratedFDeriv (by norm_cast; omega)
        ext w
        simp only [A, ContinuousMultilinearMap.domDomCongr_apply]
        rw [hd.iteratedFDeriv_succ_apply_left', hd.iteratedFDeriv_succ_apply_left']
        have hevent :
            (fun y => iteratedFDeriv ℝ (n + 1) f y
              (Fin.tail (fun q => w (Equiv.swap k.succ.castSucc k.succ.succ q)))) =ᶠ[𝓝 x]
            (fun y => iteratedFDeriv ℝ (n + 1) f y (Fin.tail w)) := by
          filter_upwards [h.eventually (by simp [← Nat.cast_add])] with y hy
          have hy' : ContDiffAt ℝ (n + 1) f y := hy.of_le (by norm_cast; omega)
          have hs := ih' hy' (Equiv.swap k.castSucc k.succ)
          have hs' := congrArg (fun L => L (Fin.tail w)) hs
          rw [tail_adjacent_swap]
          simpa only [ContinuousMultilinearMap.domDomCongr_apply] using hs'
        rw [hevent.fderiv_eq]
        congr 1
      have hgen (i : Fin (n + 1)) : ContinuousMultilinearMap.domDomCongr
          (Equiv.swap i.castSucc i.succ) A = A := by
        refine Fin.cases ?_ (fun k => ?_) i
        · simpa using hfront
        · simpa using htail k
      have hmem : σ ∈ Submonoid.closure
          (Set.range fun i : Fin (n + 1) => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        trivial
      exact Submonoid.closure_induction
        (motive := fun τ _ => ContinuousMultilinearMap.domDomCongr τ A = A)
        (fun _ hτ => by obtain ⟨i, rfl⟩ := hτ; exact hgen i)
        (by ext w; simp [ContinuousMultilinearMap.domDomCongr_apply])
        (fun τ υ _ _ hτ hυ => by
          ext w
          have hτw := congrArg (fun L => L w) hτ
          have hυw := congrArg (fun L => L (fun i => w (τ i))) hυ
          simpa only [ContinuousMultilinearMap.domDomCongr_apply, Equiv.Perm.mul_apply] using
            hυw.trans hτw)
        hmem

section Admissible

variable [FiniteDimensional ℝ E]

/-- The neighbourhood regularity in the admissible class, specialized at a
feasible point and kept at its exact finite natural order. -/
theorem IsAdmissibleOperator.contDiffAt_feasible
    (data : VIPublicData E) (G : E → E) (hG : IsAdmissibleOperator data G)
    (point : data.X) : ContDiffAt ℝ (data.p - 1 : ℕ) G point.1 := by
  obtain ⟨U, hU, hXU, hreg⟩ := hG.regularity
  exact (hreg point.1 (hXU point.2)).contDiffAt (hU.mem_nhds (hXU point.2))

/-- Every derivative returned at a feasible point by an admissible operator
is symmetric.  The only smoothness used is the source's finite
`C^(p - 1)` neighbourhood assumption. -/
theorem IsAdmissibleOperator.iteratedFDeriv_symmetric
    (data : VIPublicData E) (G : E → E) (hG : IsAdmissibleOperator data G)
    (point : data.X) (j : Fin data.p) (σ : Equiv.Perm (Fin j.1)) :
    ContinuousMultilinearMap.domDomCongr σ
      (iteratedFDeriv ℝ j.1 G point.1) = iteratedFDeriv ℝ j.1 G point.1 := by
  apply finiteContDiffAt_iteratedFDeriv_symmetric
  exact (hG.contDiffAt_feasible data G point).of_le (by
    exact_mod_cast Nat.le_pred_of_lt j.2)

/-- Canonical exact symmetric feasible oracle supplied by admissibility
alone; no global regularity or separate symmetry certificate is required. -/
noncomputable def IsAdmissibleOperator.feasibleExactSymmetricJetOracle
    (data : VIPublicData E) (G : E → E) (hG : IsAdmissibleOperator data G) :
    FeasibleExactSymmetricJetOracle data G where
  answer point := exactSymmetricJetOf E data.p G point.1
    (fun j σ => hG.iteratedFDeriv_symmetric data G point j σ)
  exact _ _ := rfl

/-- Existence form of the admissible-oracle bridge. -/
theorem admissible_has_feasibleExactSymmetricJetOracle
    (data : VIPublicData E) (G : E → E) (hG : IsAdmissibleOperator data G) :
    Nonempty (FeasibleExactSymmetricJetOracle data G) :=
  ⟨hG.feasibleExactSymmetricJetOracle data G⟩

end Admissible

end

end LeanArticleAudit.Pilot
