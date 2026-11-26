import Bilevel.ChiLiftedSelection

/-! Actual ordinary ancestor selection transports a full carrier ledger
through heterogeneous ambient variables with no branch-count factor. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiLiftedCarrier
open ChiBoundedChain ChiRecursive ChiCarrier

theorem constructed_ledger_selection_bound : ∃ Cs : ℝ,1≤Cs ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (m : ℕ) (D : Geometry F) (A : X →L[ℝ] Blocks m F),‖A‖≤1 → (∀ j I,NodeJetAdmissible (D j I)) →
      ∀ (leaf : ℕ → List ℕ → X → ℝ), (∀ j I,ContDiff ℝ 3 (leaf j I)) →
      ∀ (T : ℕ) (Cb N ℓ h : ℝ),0≤Cb → 1≤N → 0≤ℓ → 0<h →
      (∀ j I,j<T → h*Real.sqrt N≤(D j I).width) →
      (∀ I x q,q≤3 → ‖iteratedFDeriv ℝ q (leaf T I) x‖≤Cb*ledgerScale N ℓ h q) →
      ∀ (d j : ℕ),j+d=T → ∀ (I : List ℕ) (x : X) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (selectFamily m D A leaf d j I) x‖≤Cs^d*Cb*ledgerScale N ℓ h q := by
  obtain ⟨C,hC,hnode⟩ := constructed_joint_node_jets
  have hC0 : 0≤C := by linarith
  let Cs := 8*C
  have hCs : 1≤Cs := by unfold Cs;linarith
  have hCs0 : 0≤Cs := by linarith
  refine ⟨Cs,hCs,fun F _ _ _ X _ _ m D A hA hadm leaf hleaf T Cb N ℓ h hCb hN hℓ hh hwidth hbase => ?_⟩
  intro d
  induction d with
  | zero =>
    intro j hj I x q hq
    have hjT : j=T := by omega
    subst j
    simpa only [selectFamily,pow_zero,one_mul] using hbase I x q hq
  | succ d ih =>
    intro j hj I x q hq
    have hd := hadm j I
    have hw := hwidth j I (by omega)
    have hS := ledgerScale_nonneg (N:=N) (by linarith) hℓ hh.le q
    change ‖iteratedFDeriv ℝ q (fun y => ∑ i : Fin ((D j I).n+1),
      selector m j (D j I) A i y*selectFamily m D A leaf d (j+1) (child I i.val) y) x‖≤_
    apply selected_products_jet_bound m j (D j I) A
      (fun i => selectFamily m D A leaf d (j+1) (child I i.val))
      (fun i => selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val)) x q hq _ (by positivity)
    intro i
    have hs := coarser_product_ledger (selector_contDiff m j (D j I) A i 3)
      (selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val))
      C (Cs^d*Cb) N ℓ h (D j I).width hC0 (by positivity) hN hℓ hh hd.2.1 hw x q hq
      (fun k hk => (linear_jet_contraction A hA (jointSelector_contDiff m j (D j I) i 3) x k (by omega)).trans
        (hnode F (D j I) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2 m j i (A x) k (by omega)).1)
      (fun k hk => ih (j+1) (by omega) (child I i.val) x k (by omega))
    convert hs using 1
    simp only [pow_succ,Cs]
    ring

end Bilevel.ChiLiftedCarrier
