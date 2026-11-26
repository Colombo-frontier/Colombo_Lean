import Bilevel.ChiCarrierAncestorLocality
import Bilevel.ChiCarrierFineLedger
import Bilevel.ChiFinePhysicalLocality

/-! Actual active fine-piece support on the full lower-block Hilbert space,
including all frame/radial maps and every ancestor selector. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive ZeroChainSchedule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem jointFinePiece_gradient_mem {m : ℕ} (W : Fin m → Submodule ℝ E) (x : Blocks m E)
    (j : Fin m) (D : Node E) (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : 0≤D.ell) (hh : 0<D.width) (hR : 0<D.radius) (p r : ℕ)
    (hu : x j∈W j)
    (hU : ∀ k : Fin (D.n+1),k.val < r+1 → D.frame (basis k)∈W j)
    (hz : ∀ k : Fin (D.n+1),r ≤ k.val → |D.coordinates (x j) k|≤D.width/4) :
    gradient (jointFinePiece m j.val D c θ p) x∈knownSpace W := by
  let P : ChiFine.Parameters := ⟨D.ell,D.width,θ,c,hell,hh,hθ,hc,hcs⟩
  change gradient ((P.pieces D.n p ∘ D.coordinates) ∘ block m j.val) x∈knownSpace W
  apply block_composition_gradient_mem W x j
    ((P.pieces_contDiff D.n p).comp (D.coordinates_contDiff 3))
  exact WrappedPrefixLocality.carried_gradient_mem D.n (r+1) D.radius hR D.frame _
    ((P.pieces_contDiff D.n p).differentiable (by norm_num)) (x j) (W j) hu hU
      (fun k hk => P.pieces_gradient_support D.n p r _ hz k hk)

theorem selectedFinePiece_gradient_mem {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hm : j+d < m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ)
    (hblind : ∀ k P (_hk : j ≤ k) (hkt : k < j+d),
      BlindNode W x ⟨k,by omega⟩ (D k P) (r k P))
    (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : ∀ P,0≤(D (j+d) P).ell) (hh : ∀ P,0<(D (j+d) P).width)
    (hR : ∀ P,0<(D (j+d) P).radius)
    (hu : x ⟨j+d,hm⟩∈W ⟨j+d,hm⟩)
    (hU : ∀ P,∀ k : Fin ((D (j+d) P).n+1),k.val < r (j+d) P+1 →
      (D (j+d) P).frame (basis k)∈W ⟨j+d,hm⟩)
    (hz : ∀ P,∀ k : Fin ((D (j+d) P).n+1),r (j+d) P ≤ k.val →
      |(D (j+d) P).coordinates (x ⟨j+d,hm⟩) k|≤(D (j+d) P).width/4)
    (p : ℕ) : gradient (selectedFinePiece m D d j I c θ p) x∈knownSpace W := by
  apply selectFamily_gradient_mem_of_blind D _
    (fun k P => jointFinePiece_contDiff m k (D k P) c θ p) d j I hm W x r hblind
  intro P
  exact jointFinePiece_gradient_mem W x ⟨j+d,hm⟩ (D (j+d) P) c θ hc hcs hθ
    (hell P) (hh P) (hR P) p (r (j+d) P) hu (hU P) (hz P)

end Bilevel.ChiCarrier
