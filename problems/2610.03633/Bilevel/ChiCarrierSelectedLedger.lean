import Bilevel.ChiCarrierLocalLedger
import Bilevel.ChiCarrierSourceWidths

/-! Actual source recursive selected-carrier joint derivative ledger. The
induction differentiates the actual finite recursion, with all local analytic
bounds and ancestor-width conditions discharged by the construction. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

theorem source_selected_joint_ledger (A K ζ cn : ℝ) (hA : 0≤A) (hK : 1≤K)
    (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1) :
    ∃ C : ℝ,1≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r η b : ℕ → ℝ) (CR : ℝ),(∀ j,1≤r j) → (∀ j,0<η j) → (∀ j,η j≤1) →
      (∀ j,128≤cn/(η j)^2) → (∀ j,0<b j) → (∀ j,b j≤1) → 1≤CR → ζ*Real.sqrt cn≤CR →
      ∀ (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] F),
      let D := sourceGeometry initial r η b A K ζ cn CR U
      ∀ (d j t : ℕ) (I : List ℕ) (m : ℕ) (x : Blocks m F) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (jointCarrier m D d j I t) x‖≤
        C^(t+1)*ledgerScale (((D (j+t) []).n:ℝ)+1) (D (j+t) []).ell (D (j+t) []).width q := by
  obtain ⟨Cb,hCb,hbase⟩ := source_geometry_local_ledger A K ζ cn hA hK hζ hζ1 hcn
  obtain ⟨Cs,hCs,hstep⟩ := constructed_selected_ledger_step
  let C := Cb+Cs
  have hC : 1≤C := by unfold C;linarith
  have hC0 : 0≤C := by linarith
  have hCbC : Cb≤C := by unfold C;linarith
  have hCsC : Cs≤C := by unfold C;linarith
  refine ⟨C,hC,fun F _ _ _ initial hl hw r η b CR hr hη hη1 hlen hb hb1 hCR hCRcn U => ?_⟩
  dsimp only
  let D := sourceGeometry initial r η b A K ζ cn CR U
  have hp := parentScale_positive initial r η hl hw hr hη
  have hadm (j : ℕ) (I : List ℕ) :
      0≤(D j I).ell ∧ 0<(D j I).width ∧ (D j I).width≤(D j I).radius ∧
      0<(D j I).parentWidth ∧ (D j I).parentWidth≤(D j I).radius :=
    sourceNode_admissible A K ζ cn (η j) CR _ _ (r j) (b j) (U j I)
      hK hζ hζ1 (hη j) (hη1 j) hCR (hp j).1 (hp j).2 (hr j) (hb j) (hb1 j)
  have hlocal := hbase F initial hl hw r η b CR hr hη hη1 hlen hb hb1 hCR hCRcn U
  have hwidth := source_geometry_ancestor_width initial r η b A K ζ cn CR U
    hl hw hr hη hη1 hcn hcn1 hlen
  have hmain (t : ℕ) : ∀ (d j : ℕ) (I : List ℕ) (m : ℕ) (x : Blocks m F) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (jointCarrier m D d j I t) x‖≤
        C^(t+1)*ledgerScale (((D (j+t) []).n:ℝ)+1) (D (j+t) []).ell (D (j+t) []).width q := by
    induction t with
    | zero =>
      intro d j I m x q hq
      have hb₀ := hlocal d j I m x q hq
      have hs : 0≤ledgerScale (((D j I).n:ℝ)+1) (D j I).ell (D j I).width q :=
        ledgerScale_nonneg (by positivity) (hadm j I).1 (hadm j I).2.1.le q
      have hb₁ := mul_le_mul_of_nonneg_right hCbC hs
      simpa only [Nat.add_zero,Nat.zero_add,pow_one] using hb₀.trans hb₁
    | succ t ih =>
      intro d j I m x q hq
      have ht := hadm (j+(t+1)) []
      have hN : 1≤((D (j+(t+1)) []).n:ℝ)+1 := by
        have := Nat.cast_nonneg (α:=ℝ) (D (j+(t+1)) []).n
        linarith
      have hs : 0≤ledgerScale (((D (j+(t+1)) []).n:ℝ)+1)
          (D (j+(t+1)) []).ell (D (j+(t+1)) []).width q :=
        ledgerScale_nonneg (by positivity) ht.1 ht.2.1.le q
      cases d with
      | zero =>
        change ‖iteratedFDeriv ℝ q (fun _ : Blocks m F => (0:ℝ)) x‖≤_
        by_cases hq0 : q=0
        · subst q
          rw [norm_iteratedFDeriv_zero,norm_zero]
          exact mul_nonneg (pow_nonneg hC0 _) hs
        · rw [iteratedFDeriv_const_of_ne hq0,Pi.zero_apply,norm_zero]
          exact mul_nonneg (pow_nonneg hC0 _) hs
      | succ d =>
        change ‖iteratedFDeriv ℝ q (fun y => ∑ i : Fin ((D j I).n+1),
          jointSelector m j (D j I) i y*jointCarrier m D d (j+1) (child I i.val) t y) x‖≤_
        have hd := hadm j I
        have hb₀ := hstep F (D j I) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2
          m j (fun i => jointCarrier m D d (j+1) (child I i.val) t)
          (fun i => jointCarrier_contDiff m D d (j+1) (child I i.val) t 3)
          (C^(t+1)) (((D (j+(t+1)) []).n:ℝ)+1)
          (D (j+(t+1)) []).ell (D (j+(t+1)) []).width
          (pow_nonneg hC0 _) hN ht.1 ht.2.1
          (hwidth j (j+(t+1)) (by omega) I []) x q hq
          (fun i a ha => by
            simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
              ih d (j+1) (child I i.val) m x a (by omega))
        have hb₁ := mul_le_mul_of_nonneg_right hCsC
          (mul_nonneg (pow_nonneg hC0 (t+1)) hs)
        apply hb₀.trans
        convert hb₁ using 1 <;> simp only [pow_succ] <;> ring
  intro d j t I m x q hq
  exact hmain t d j I m x q hq

end Bilevel.ChiCarrier
