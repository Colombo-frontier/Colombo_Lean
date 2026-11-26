import Bilevel.ChiOuterUpperBase
import Bilevel.ChiOuterCoerciveGeometry
import Bilevel.ChiSourceCoarseFamily

/-! Exact finite trace decomposition into the actual upper base, selected
coarse carriers, centered fine frontier, and unselected public penalties. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry RadialWrapper ChiExtensionCalibration
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem outerPayload_carrier_sum (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ)
    (z : Joint E (Blocks m F)) :
    outerSelected m M (fun i => jointPayload m D d 0 [i.val]) z=
      ∑ k : Fin (d+1),outerCarrier m M D d k.val z := by
  simp only [outerSelected,outerCarrier,jointPayload_trace,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem jointOuter_expanded (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (z : Joint E (Blocks m F)) :
    jointOuter m M ν D ρ R d 1 z=
      macroValue M.n M.ell M.width ν M.radius M.frame z.fst+
        outerReleaseCorrection m M (fun i => D 0 [i.val]) z+
        outerSelected m M (fun i => jointPayload m D d 0 [i.val]) z+
        publicValue ρ R d 0 (padded z.snd) := by
  simp only [jointOuter,one_smul]
  change macroValue M.n M.ell M.width ν M.radius M.frame z.fst+
    (∑ i : Fin (M.n+1),(((D 0 [i.val]).release (block m 0 z.snd)-1)*wrappedResidual M i z.fst+
      jointPayload m D d 0 [i.val] z.snd*wrappedSelector M i z.fst))+publicValue ρ R d 0 (padded z.snd)=
    macroValue M.n M.ell M.width ν M.radius M.frame z.fst+
    (∑ i : Fin (M.n+1),wrappedResidual M i z.fst*((D 0 [i.val]).release (block m 0 z.snd)-1))+
    (∑ i : Fin (M.n+1),wrappedSelector M i z.fst*jointPayload m D d 0 [i.val] z.snd)+publicValue ρ R d 0 (padded z.snd)
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ i : Fin (M.n+1),((D 0 [i.val]).release (block m 0 z.snd)-1)*wrappedResidual M i z.fst)=
      ∑ i : Fin (M.n+1),wrappedResidual M i z.fst*((D 0 [i.val]).release (block m 0 z.snd)-1) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ i : Fin (M.n+1),jointPayload m D d 0 [i.val] z.snd*wrappedSelector M i z.fst)=
      ∑ i : Fin (M.n+1),wrappedSelector M i z.fst*jointPayload m D d 0 [i.val] z.snd := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1,h2]
  ring

theorem upperBase_trace (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (z : Joint E (Blocks m F)) :
    jointOuter m M ν D ρ R d 1 z=
      upperBase m M ν D d (ρ 0) (R 0) z+
        ∑ i : Fin d,outerCarrier m M D d (i.val+1) z+
        ∑ i : Fin d,bowl (ρ (i.val+1)) (R (i.val+1)) (block m (i.val+1) z.snd) := by
  rw [jointOuter_expanded,outerPayload_carrier_sum,publicValue_sum,
    Fin.sum_univ_succ (fun k : Fin (d+1) => outerCarrier m M D d k.val z),
    Fin.sum_univ_succ (fun k : Fin (d+1) => bowl (ρ (0+k.val)) (R (0+k.val)) (padded z.snd (0+k.val)))]
  simp only [Fin.val_zero,Fin.val_succ,Nat.zero_add,upperBase,baseLower,baseRadial,padded]
  ring

theorem coarse_fine_trace (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ)
    (z : Joint E (Blocks m F)) :
    (∑ i : Fin (d+1),coarseFamily m M D (d+1) i z)+outerFineFrontier m M D (d+1) z=
      ∑ i : Fin (d+1),outerCarrier m M D (d+1) (i.val+1) z := by
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  have hsmall (i : Fin d) : i.castSucc.val+1≠d+1 := by change i.val+1≠d+1;omega
  simp only [coarseFamily,Fin.val_last,if_pos rfl]
  simp only [hsmall,if_false,if_true,outerDeepestA]
  ring

theorem upperBase_coarse_fine_trace (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (z : Joint E (Blocks m F)) :
    jointOuter m M ν D ρ R (d+1) 1 z=
      upperBase m M ν D (d+1) (ρ 0) (R 0) z+
        (∑ i : Fin (d+1),coarseFamily m M D (d+1) i z)+outerFineFrontier m M D (d+1) z+
        ∑ i : Fin (d+1),bowl (ρ (i.val+1)) (R (i.val+1)) (block m (i.val+1) z.snd) := by
  rw [upperBase_trace,← coarse_fine_trace]
  ring

end Bilevel.ChiOuter
