(** Federer (1969), 1.7.8, p. 34: Hodge pairing invariance for every unit
    volume, with the corrected mixed-degree sign. Erratum p. 1, book p. 34
    lines 29-30: the mixed identity has sign (-1)^{p(n-p)} and beta has
    degree n-p. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior LinearBasis
  GramSchmidt OrthonormalisationUP ExteriorGrading ExteriorNorm
  FiniteExteriorPowers AlternatingCoordinates AlternatingPairing
  HodgeMaps HodgePairingBasis UnitTopVolume TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [hodge_pairing]: Federer 1.7.8,
    p. 34, fifth conclusion: <star xi, star phi> = <xi,phi>.
    No restriction on the sign of the chosen unit volume is imposed. *)
Theorem hodge_pairing (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b)
    (E : exterior_power V n) (hE : exterior_norm h2 hB E = 1)
    p (hp : (p <= n)%N) (x : exterior_power V p) (phi : A_m V R^o p) :
  pairing (hodge_vector h2 hB E hp x) (hodge_covector h2 hB E hp phi) = pairing x phi.
Proof.
have [e [he horth]] := @orthonormal_basis_exists R V B hB n b hb.
have ho := orthonormalisation_orthonormal horth.
have [c [hc hc2]] := @unit_top_volume_scalar R h2 V B hB n e he ho E hE.
rewrite hc hodge_vector_volume_scale hodge_covector_volume_scale
  (bilZl (@pairing_bilinear R V R^o (n-p)))
  (bilZr (@pairing_bilinear R V R^o (n-p))) scalerA -expr2 hc2 scale1r.
exact: (@hodge_pairing_basis_volume R h2 V B hB n e he ho p hp x phi).
Qed.
