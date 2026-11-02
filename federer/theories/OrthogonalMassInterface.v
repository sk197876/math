(** Federer (1969), 1.8.4, pp. 40-41: the product
    equation in the public sealed mass interface. The abstract
    theorem remains available for any supplied norm specifications. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors SubspaceCarrier InnerProductUP
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts LinearBasis
  Comass Mass OrthogonalMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [mass_orthogonal_product]: Federer 1.8.4,
    pp. 40-41, mass(xi wedge eta)=mass(xi) mass(eta) for
    orthogonally supported factors with either factor simple,
    specialised to the actual sealed public mass functions. *)
Theorem mass_orthogonal_product (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (S T : subspace V)
    (hST : forall u v, S u -> T v -> B u v = 0)
    p q (hp : (0 < p)%N) (hq : (0 < q)%N)
    (x0 : exterior_power (subspace_space S) p)
    (y0 : exterior_power (subspace_space T) q) :
  (simple (exterior_power_map (subspace_inclusion S) p x0) \/
    simple (exterior_power_map (subspace_inclusion T) q y0)) ->
  mass h2 hB he (leq_trans hp (leq_addr q p))
    (exterior_product (exterior_power_map (subspace_inclusion S) p x0)
      (exterior_power_map (subspace_inclusion T) q y0)) =
  mass h2 hB he hp (exterior_power_map (subspace_inclusion S) p x0) *
  mass h2 hB he hq (exterior_power_map (subspace_inclusion T) q y0).
Proof.
move=> hs.
exact (@orthogonal_mass_product R h2 V B hB n e he S T hST p q hp hq
  (@comass R h2 V B hB n e he p hp) (@comass R h2 V B hB n e he q hq)
  (@comass R h2 V B hB n e he (p+q) (leq_trans hp (leq_addr q p)))
  (@comassP R h2 V B hB n e he p hp) (@comassP R h2 V B hB n e he q hq)
  (@comassP R h2 V B hB n e he (p+q) (leq_trans hp (leq_addr q p)))
  x0 y0 _ _ _ hs (@massP R h2 V B hB n e he p hp _)
  (@massP R h2 V B hB n e he q hq _)
  (@massP R h2 V B hB n e he (p+q) (leq_trans hp (leq_addr q p)) _)).
Qed.
