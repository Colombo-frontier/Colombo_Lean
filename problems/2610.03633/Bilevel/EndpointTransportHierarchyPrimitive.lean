import Bilevel.EndpointTransportNormalTrace
import Bilevel.EndpointTransportUpperReadout
import Bilevel.EndpointTransportHybridWitness

/-! A single actual physical hybrid Primitive from the complete constructed
normal extension and upper base. Only their numerical budgets remain as
inputs; inverse, unique response, and original recursive mean are derived. -/
noncomputable section
set_option maxHeartbeats 1600000
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiRecursive ChiCarrier ChiOuter ChiExtension ChiExtensionCalibration
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem physical_hierarchy_primitive_of_budgets {D : ℕ} {L κ ρg : ℝ}
    (hL : 0<L) (hκ : 3200≤κ) (hρg : 0≤ρg) (j : ℕ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (P : ChiFine.Parameters) (ρ R : ℕ → ℝ)
    (coarseIndex radialIndex : Fin (j+1) → Fin (2*(j+1))) (fineIndex : Fin (2*(j+1)))
    (hw : ∀ i : Fin (j+1),0<(G (i.val+1) []).width) (hR : ∀ i : Fin (j+1),0<R (i.val+1)) :
    let J := j+1
    let dn := normalCoefficient L J
    let core := physicalHierarchyExtension Q M G P J (2*J) coarseIndex radialIndex fineIndex ρ R dn
    let base := physicalUpperBase J Q M ν G J (ρ 0) (R 0)
    (∀ z,‖iteratedFDeriv ℝ 2 core z‖≤1/12) →
    (∀ z,‖iteratedFDeriv ℝ 3 core z‖≤ρg/(3*(3*(L/κ)/2))) →
    (∀ z,‖iteratedFDeriv ℝ 2 base z‖≤L) →
    (∀ x t,‖gradient (fun w => base (pack x w)) t‖≤3*L/4) →
    ∃ Pr : Model.Primitive (X:=HybridOuter E (Blocks J (Block D)) D)
        (Y:=HybridVariables (Blocks J (Block D)) (Normals (2*J)) (EndpointTransportNormalization.interiors κ) D)
        (L/κ) L L L ρg,
      (∀ x y,Pr.f x y=base (pack x.fst.fst y.fst)+dn*normalReadout (2*J) y.snd) ∧
      ∃ (hExt : ContDiff ℝ 3 (physicalExtension core))
        (hExt2 : ∀ z,‖iteratedFDeriv ℝ 2 (physicalExtension core) z‖≤(1:ℝ)/12),
      (∀ x y,Pr.g x y=sourceHybridLower L κ Q (physicalExtension core) hExt
        ⟨1/12,by norm_num⟩ hExt2 (by change (1:ℝ)/12<1;norm_num) (pack x y)) ∧
      ∃ r : Pr.Response,
        (∀ x,r.y x=ChiHybrid.responseOfExtension (physicalExtension core) (sourceHybridTangent L κ Q) x) ∧
        (∀ x,Pr.hyperobjective r x=jointOuter (J+1) M ν G ρ R J
          (EndpointTransportNormalization.gain κ) (sourceCoordinates J D x)) ∧
        (∀ x y,Pr.IsLowerSolution x y ↔ y=ChiHybrid.responseOfExtension (physicalExtension core) (sourceHybridTangent L κ Q) x) := by
  dsimp only
  intro h2 h3 hbase2 hbase1
  let J := j+1
  let n := EndpointTransportNormalization.interiors κ
  let dn := normalCoefficient L J
  let core := physicalHierarchyExtension Q M G P J (2*J) coarseIndex radialIndex fineIndex ρ R dn
  let base := physicalUpperBase J Q M ν G J (ρ 0) (R 0)
  let b : Normals (2*J) := dn • normalOnes (2*J)
  have hcore := physicalHierarchyExtension_contDiff Q M G P J (2*J) coarseIndex radialIndex fineIndex ρ R dn hw
  have hbase := physicalUpperBase_contDiff J Q M ν G J (ρ 0) (R 0)
  have hdn : dn≠0 := (normalCoefficient_pos hL (by dsimp [J];omega)).ne'
  have hb : ‖b‖≤L/4 := by
    have h := source_readout_gradient_norm hL J (by dsimp [J];omega) 0
    rw [(weightedReadout_hasGradientAt (2*J) dn 0).gradient] at h
    exact h.le
  have hbinner (v : Normals (2*J)) : ⟪b,v⟫=dn*normalReadout (2*J) v := by
    rw [show b=dn • normalOnes (2*J) from rfl,real_inner_smul_left,
      ← InnerProductSpace.toDual_apply,normalOnes_toDual]
  let Ext : Joint (HybridOuter E (Blocks J (Block D)) D) (HybridVariables (Blocks J (Block D)) (Normals (2*J)) n D) → ℝ :=
    physicalExtension core
  have hExt : ContDiff ℝ 3 Ext := physicalExtension_contDiff hcore
  have hExt2 (z) : ‖iteratedFDeriv ℝ 2 Ext z‖≤(1:ℝ)/12 :=
    (physicalExtension_jet_bound hcore z 2 (by norm_num)).trans (h2 _)
  have hExt3 (z) : ‖iteratedFDeriv ℝ 3 Ext z‖≤ρg/(3*(3*(L/κ)/2)) :=
    (physicalExtension_jet_bound hcore z 3 (by norm_num)).trans (h3 _)
  have hzero (x : HybridOuter E (Blocks J (Block D)) D) (t : HybridTangent (Blocks J (Block D)) n D) :
      Ext (pack x (pack t (0:Normals (2*J))))=0 :=
    physicalExtension_zero_trace
      (physicalHierarchyExtension_zero_trace Q M G P J (2*J) coarseIndex radialIndex fineIndex ρ R dn hw) x t
  have hf : ContDiff ℝ 3 (hybridUpper (fun x t => base (pack x t)) b) :=
    physicalUpper_contDiff base hbase b
  have hf2 (z) : ‖iteratedFDeriv ℝ 2 (hybridUpper (fun x t => base (pack x t)) b) z‖≤L :=
    (physicalUpper_second_bound base hbase b z).trans (hbase2 _)
  have hfy (x) (y) : ‖gradient (fun w => hybridUpper (fun x t => base (pack x t)) b (pack x w)) y‖≤L :=
    (physicalUpper_lower_gradient_bound base hbase b hbase1 x y).trans (by linarith only [hb])
  have htrace (x : HybridOuter E (Blocks J (Block D)) D) (t : HybridTangent (Blocks J (Block D)) n D) :
      base (pack x.fst.fst t)+⟪b,(gradient Ext (pack x (pack t (0:Normals (2*J))))).snd.snd⟫=
        physicalOuter Q M ν G ρ R J x.fst.fst (padded t.fst) t.snd := by
    exact physicalExtension_readout_trace hcore base
      (fun p => physicalOuter Q M ν G ρ R J p.fst (padded p.snd.fst) p.snd.snd) dn
      (physicalHierarchyExtension_objective_trace Q M ν G P j (2*J) coarseIndex radialIndex fineIndex ρ R dn hdn hw hR) x t
  obtain ⟨Pr,hfPr,hgPr,r,hr,hmean,hunique⟩ := source_hybrid_witness_of_trace hL hκ hρg Q M ν G ρ R
    Ext hExt ⟨1/12,by norm_num⟩ hExt2 (by change (1:ℝ)/12<1;norm_num) (by norm_num)
    hzero hExt3 (fun x t => base (pack x t)) b hf hf2 hfy htrace
  refine ⟨Pr,?_,hExt,hExt2,hgPr,r,hr,hmean,hunique⟩
  intro x y
  rw [hfPr,hbinner]

end Bilevel.EndpointTransportResponse
