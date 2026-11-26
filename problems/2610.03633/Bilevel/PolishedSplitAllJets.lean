import Bilevel.PolishedLiteralAllJets
import Bilevel.EndpointTransportPayloadSize

/-!
Arbitrary mixed-order uniqueness for the actual BOUNDED recursive cutoff
and split-endpoint selectors. The a and b variables remain independent
off the response graph. No derivative-order ceiling is imposed.
-/
noncomputable section
open scoped BigOperators ContDiff
namespace Bilevel.PolishedSplitAllJets
open ChiBoundedChain ChiRecursive PrimitiveGeometry PartialLegendre
open PolishedLiteral.AllJets (scalar_plateau_flat scalar_linear_flat
  product_flat_left product_flat_right composition_flat)

theorem evenGate_all_orders_flat (k : ℕ) (t : ℝ) (ht : |t| ≤ 1/2) :
    iteratedDeriv k evenGate t=0 := by
  cases k with
  | zero => simpa only [iteratedDeriv_zero] using evenGate_zero ht
  | succ k =>
    exact scalar_plateau_flat (fun j => evenGate_contDiff j)
      (uniqueDiffOn_Icc (by norm_num : -(1/2 : ℝ) < 1/2))
      (fun _ h => evenGate_zero (abs_le.mpr h)) (k+1) (by omega) t (abs_le.mp ht)

theorem selector_succ_all_orders_flat {n : ℕ} (i : Fin n) (z : Space n)
    (hz : |z i.castSucc| ≤ 1/2) (k : ℕ) :
    iteratedFDeriv ℝ k (selector n i.succ) z=0 := by
  apply product_flat_left k
    ((evenGate_contDiff k).comp (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).contDiff)
    (tailMask_contDiff i.succ k) z
  intro j _
  exact scalar_linear_flat j (evenGate_contDiff j) (EuclideanSpace.proj (𝕜 := ℝ) i.castSucc)
    z (evenGate_all_orders_flat j _ hz)

theorem selector_large_tail_all_orders_flat {n : ℕ} (i l : Fin (n+1)) (z : Space n)
    (hil : i ≤ l) (hz : 1/2 ≤ |z l|) (k : ℕ) :
    iteratedFDeriv ℝ k (selector n i) z=0 := by
  have he : 1 ≤ tailEnergy i z := by
    have hh := coordinate_energy_le i l z hil
    simpa only [coordinateCutoff_one hz,one_pow] using hh
  revert he
  refine Fin.cases (fun he => PolishedLiteral.AllJets.tailMask_flat 0 z he k) (fun j he => ?_) i
  exact product_flat_right k
    ((evenGate_contDiff k).comp (EuclideanSpace.proj (𝕜 := ℝ) j.castSucc).contDiff)
    (tailMask_contDiff j.succ k) z
    (fun q _ => PolishedLiteral.AllJets.tailMask_flat j.succ z he q)

theorem selector_before_later_all_orders_flat {n : ℕ} (i l : Fin (n+1)) (z : Space n)
    (k q : ℕ) (hil : i < l) (hl : iteratedFDeriv ℝ q (selector n l) z ≠ 0) :
    iteratedFDeriv ℝ k (selector n i) z=0 := by
  revert hil hl
  refine Fin.cases (by intro h; exact False.elim (Fin.not_lt_zero i h)) (fun j => ?_) l
  intro hij hj
  have hz : 1/2 < |z j.castSucc| := by
    by_contra! hz
    exact hj (selector_succ_all_orders_flat j z hz q)
  apply selector_large_tail_all_orders_flat i j.castSucc z _ hz.le k
  change i.val ≤ j.val
  change i.val < j.val+1 at hij
  omega

theorem bounded_selector_all_orders_unique {n : ℕ} (i l : Fin (n+1)) (z : Space n) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (selector n i) z ≠ 0)
    (hl : iteratedFDeriv ℝ q (selector n l) z ≠ 0) : i=l := by
  rcases lt_trichotomy i l with h | h | h
  · exact False.elim (hi (selector_before_later_all_orders_flat i l z k q h hl))
  · exact h
  · exact False.elim (hl (selector_before_later_all_orders_flat l i z q k h hi))

section Composition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} (f : E → Space n) (hf : ∀ k : ℕ,ContDiff ℝ k f)

include hf in
theorem selector_composition_all_orders_unique (i l : Fin (n+1)) (x : E) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (selector n i ∘ f) x ≠ 0)
    (hl : iteratedFDeriv ℝ q (selector n l ∘ f) x ≠ 0) : i=l := by
  have hlatent (a : Fin (n+1)) (s : ℕ)
      (ha : iteratedFDeriv ℝ s (selector n a ∘ f) x ≠ 0) :
      ∃ j ≤ s,iteratedFDeriv ℝ j (selector n a) (f x) ≠ 0 := by
    by_contra! hz
    exact ha (composition_flat s (hf s) (selector_contDiff n s a) x hz)
  obtain ⟨a,_,ha⟩ := hlatent i k hi
  obtain ⟨b,_,hb⟩ := hlatent l q hl
  exact bounded_selector_all_orders_unique i l (f x) a b ha hb

include hf in
theorem selected_atom_jet_has_selector (g : E → ℝ) (hg : ∀ k : ℕ,ContDiff ℝ k g)
    (i : Fin (n+1)) (x : E) (k : ℕ)
    (hi : iteratedFDeriv ℝ k (fun y => selector n i (f y)*g y) x ≠ 0) :
    ∃ j ≤ k,iteratedFDeriv ℝ j (selector n i) (f x) ≠ 0 := by
  by_contra! hz
  apply hi
  apply product_flat_left k ((selector_contDiff n k i).comp (hf k)) (hg k) x
  intro j hj
  exact composition_flat j (hf j) (selector_contDiff n j i) x
    (fun a ha => hz a (ha.trans hj))

include hf in
theorem selected_atoms_all_orders_unique (g : Fin (n+1) → E → ℝ)
    (hg : ∀ (i : Fin (n+1)) (k : ℕ),ContDiff ℝ k (g i)) (i l : Fin (n+1)) (x : E) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (fun y => selector n i (f y)*g i y) x ≠ 0)
    (hl : iteratedFDeriv ℝ q (fun y => selector n l (f y)*g l y) x ≠ 0) : i=l := by
  obtain ⟨a,_,ha⟩ := selected_atom_jet_has_selector f hf (g i) (hg i) i x k hi
  obtain ⟨b,_,hb⟩ := selected_atom_jet_has_selector f hf (g l) (hg l) l x q hl
  exact bounded_selector_all_orders_unique i l (f x) a b ha hb

end Composition

theorem split_selector_all_orders_unique {n : ℕ} (i l : Fin (n+1)) (z : ChiSplitChain.Latent n) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (fun y : ChiSplitChain.Latent n => selector n i y.snd) z ≠ 0)
    (hl : iteratedFDeriv ℝ q (fun y : ChiSplitChain.Latent n => selector n l y.snd) z ≠ 0) : i=l :=
  selector_composition_all_orders_unique
    (jointSndLinear : ChiSplitChain.Latent n →L[ℝ] Space n)
    (fun _ => (jointSndLinear : ChiSplitChain.Latent n →L[ℝ] Space n).contDiff) i l z k q hi hl

theorem split_frontier_atoms_all_orders_unique {n : ℕ} (i l : Fin (n+1))
    (z : ChiSplitChain.Latent n) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (fun y : ChiSplitChain.Latent n =>
      -selector n i y.snd*(ZeroChainPotential.phi (y.fst i)-ZeroChainPotential.phi 0)) z ≠ 0)
    (hl : iteratedFDeriv ℝ q (fun y : ChiSplitChain.Latent n =>
      -selector n l y.snd*(ZeroChainPotential.phi (y.fst l)-ZeroChainPotential.phi 0)) z ≠ 0) : i=l := by
  let f := (jointSndLinear : ChiSplitChain.Latent n →L[ℝ] Space n)
  let g := fun a : Fin (n+1) => fun y : ChiSplitChain.Latent n =>
    -(ZeroChainPotential.phi (y.fst a)-ZeroChainPotential.phi 0)
  have hg (a : Fin (n+1)) (s : ℕ) : ContDiff ℝ s (g a) :=
    (((ZeroChainPotential.phi_contDiff s).comp (ChiSplitChain.sourceProjection a).contDiff).sub contDiff_const).neg
  apply selected_atoms_all_orders_unique f (fun _ => f.contDiff) g hg i l z k q
  · simpa only [g,f,Function.comp_apply,neg_mul,mul_neg] using hi
  · simpa only [g,f,Function.comp_apply,neg_mul,mul_neg] using hl

theorem physicalCoordinates_contDiff_all {n D : ℕ} (Q : EndpointTransportResponse.Rotations n D)
    (N : Node (EndpointTransportResponse.Block D)) (k : ℕ) :
    ContDiff ℝ k (EndpointTransportResponse.physicalCoordinates Q N) :=
  (ChiSplitChain.readout (EndpointTransportResponse.sourceReadout Q N.frame)
    (EndpointTransportResponse.targetReadout Q N.frame)).contDiff.comp
      (RadialWrapper.compress_contDiff (EndpointTransportMatrix.gamma n*N.radius) k)

theorem physical_selector_all_orders_unique {n D : ℕ} (Q : EndpointTransportResponse.Rotations n D)
    (N : Node (EndpointTransportResponse.Block D)) (i l : Fin (N.n+1))
    (Y : EndpointTransportResponse.Physical n D) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (EndpointTransportResponse.physicalSelector Q N i) Y ≠ 0)
    (hl : iteratedFDeriv ℝ q (EndpointTransportResponse.physicalSelector Q N l) Y ≠ 0) : i=l :=
  selector_composition_all_orders_unique
    (fun y => N.width⁻¹ • (EndpointTransportResponse.physicalCoordinates Q N y).snd)
    (fun s => ((jointSndLinear : ChiSplitChain.Latent N.n →L[ℝ] Space N.n).contDiff.comp
      (physicalCoordinates_contDiff_all Q N s)).const_smul N.width⁻¹)
    i l Y k q hi hl

theorem physical_residual_all_orders_unique {n D : ℕ} (Q : EndpointTransportResponse.Rotations n D)
    (N : Node (EndpointTransportResponse.Block D)) (i l : Fin (N.n+1))
    (Y : EndpointTransportResponse.Physical n D) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (EndpointTransportResponse.physicalResidual Q N i) Y ≠ 0)
    (hl : iteratedFDeriv ℝ q (EndpointTransportResponse.physicalResidual Q N l) Y ≠ 0) : i=l := by
  let f := fun y => N.width⁻¹ • (EndpointTransportResponse.physicalCoordinates Q N y).snd
  let g := fun a : Fin (N.n+1) => fun y => (N.ell*N.width^2)*
    (-ZeroChainPotential.phi (N.width⁻¹*(EndpointTransportResponse.physicalCoordinates Q N y).fst a))
  have hf (s : ℕ) : ContDiff ℝ s f :=
    ((jointSndLinear : ChiSplitChain.Latent N.n →L[ℝ] Space N.n).contDiff.comp
      (physicalCoordinates_contDiff_all Q N s)).const_smul N.width⁻¹
  have hg (a : Fin (N.n+1)) (s : ℕ) : ContDiff ℝ s (g a) :=
    contDiff_const.mul (((ZeroChainPotential.phi_contDiff s).comp
      (((ChiSplitChain.sourceProjection a).contDiff.comp (physicalCoordinates_contDiff_all Q N s)).const_smul N.width⁻¹)).neg)
  have he (a : Fin (N.n+1)) : EndpointTransportResponse.physicalResidual Q N a=
      fun y => selector N.n a (f y)*g a y := by
    funext y
    dsimp [EndpointTransportResponse.physicalResidual,ChiSplitChain.residualTerm,f,g]
    ring
  rw [he i] at hi
  rw [he l] at hl
  exact selected_atoms_all_orders_unique f hf g hg i l Y k q hi hl

/-- Any prescribed finite jet order, including mixed orders of distinct
atoms, has at most one active selector in the actual physical lift. -/
theorem physical_prescribed_order_one_active {n D : ℕ} (Q : EndpointTransportResponse.Rotations n D)
    (N : Node (EndpointTransportResponse.Block D)) (Y : EndpointTransportResponse.Physical n D) (K : ℕ) :
    Set.Subsingleton {i : Fin (N.n+1) | ∃ k ≤ K,
      iteratedFDeriv ℝ k (EndpointTransportResponse.physicalSelector Q N i) Y ≠ 0} := by
  intro i hi l hl
  obtain ⟨k,_,hi⟩ := hi
  obtain ⟨q,_,hl⟩ := hl
  exact physical_selector_all_orders_unique Q N i l Y k q hi hl

end Bilevel.PolishedSplitAllJets
