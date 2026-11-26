import Bilevel.TransportNetworkObservation

/-! Projection information in a transported response is exactly the source
projection information. This proves the algebraic consistency of the stronger
observer's vector and frame-projection disclosures. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.TransportNetwork
open EuclideanGaussian OrthogonalAction

theorem forward_projection_information {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (z : Latent n d) (e : Edge n) (q : Space d) :
    queryObservation T hT (dst e) (forwardObservation e q z) z =
      queryObservation T hT (src e) q z := by
  funext i
  change ⟪z.2 e • q,frame T hT z (dst e) i⟫ = ⟪q,frame T hT z (src e) i⟫
  rw [← edge_frame T hT z e i]
  exact (isometry d (z.2 e)).inner_map_map q (frame T hT z (src e) i)

theorem reverse_edge_frame {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (z : Latent n d) (e : Edge n) (i : Fin T) :
    (z.2 e)⁻¹ • frame T hT z (dst e) i = frame T hT z (src e) i := by
  rw [← edge_frame T hT z e i,inv_smul_smul]

theorem reverse_projection_information {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (z : Latent n d) (e : Edge n) (q : Space d) :
    queryObservation T hT (src e) (reverseObservation e q z) z =
      queryObservation T hT (dst e) q z := by
  funext i
  change ⟪(z.2 e)⁻¹ • q,frame T hT z (src e) i⟫ = ⟪q,frame T hT z (dst e) i⟫
  rw [← reverse_edge_frame T hT z e i]
  exact (isometry d (z.2 e)⁻¹).inner_map_map q (frame T hT z (dst e) i)

theorem named_projection_information {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (z : Latent n d) (v : Vertex n) (i j : Fin T) :
    queryObservation T hT v (namedObservation T hT v i z) z j = if i=j then 1 else 0 :=
  (orthonormal_iff_ite.mp (frame_orthonormal T hT z v)) i j

end Bilevel.TransportNetwork
