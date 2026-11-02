(** Federer (1969), 1.7.8, p. 34: the vector and covector wedge-star
    identities. The linear wedge identities hold for every top vector E;
    when E has unit norm, gamma(E) is its dual unit volume, as in the
    printed covector identity. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior InnerExteriorIsomorphism
  LinearBasis GramSchmidt OrthonormalisationUP ExteriorGrading ExteriorNorm
  ExteriorCovectorInner ExteriorDeterminant ExteriorHomogeneousProducts
  AlternatingCoordinates AlternatingPairing FiniteExteriorPowers ScalarCoefficients
  HodgeMaps HodgeWedgeBasis HodgeAlgebraCompatibility TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [hodge_vector_wedge]: Federer 1.7.8,
    p. 34, second conclusion: xi wedge star eta = (xi dot eta) E.
    The proof also establishes the identity when E is not unit. *)
Theorem hodge_vector_wedge (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b) (E : exterior_power V n)
    p (hp : (p <= n)%N) (x y : exterior_power V p) :
  exterior_reindex (subnKC hp) (exterior_product x (hodge_vector h2 hB E hp y)) =
    exterior_inner_form h2 hB x y *: E.
Proof.
have [e [he horth]] := @orthonormal_basis_exists R V B hB n b hb.
have ho := orthonormalisation_orthonormal horth.
pose c : R := @top_coordinate R h2 n V e he E.
have hc : E = c *: e_lambda e (val (Lambda_top n)) := @top_expansion R h2 n V e he E.
rewrite hc hodge_vector_volume_scale
  (bilZr (@exterior_product_bilinear R V p (n-p))) linearZ.
change (c *: exterior_reindex (subnKC hp)
  (exterior_product x (hodge_vector h2 hB (e_lambda e (val (Lambda_top n))) hp y)) =
  exterior_inner_form h2 hB x y *: (c *: e_lambda e (val (Lambda_top n)))).
rewrite (@hodge_vector_wedge_basis_volume R h2 V B hB n e he ho p hp x y).
by rewrite !scalerA mulrC.
Qed.

(** Source for [hodge_covector_wedge]: Federer 1.7.8,
    p. 34, fourth conclusion: phi wedge star psi equals
    their covector inner product times the dual unit top covector.
    Gamma(E) is used explicitly; it is dual to E when E is unit. *)
Theorem hodge_covector_wedge (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (b : 'I_n -> V) (hb : is_basis b) (E : exterior_power V n)
    p (hp : (p <= n)%N) (phi psi : A_m V R^o p) :
  form_reindex (subnKC hp)
    (form_wedge h2 (scalar_bilinear R) phi (hodge_covector h2 hB E hp psi)) =
  exterior_covector_inner h2 hB hb phi psi *: inner_exterior_form h2 hB E.
Proof.
have [g [_ hgi]] := @inner_exterior_inverse_exists R h2 V B hB n b hb p.
rewrite -(hgi phi) -(hgi psi) hodge_polarity_diagram
  -inner_exterior_form_wedge inner_exterior_form_reindex
  (@hodge_vector_wedge R h2 V B hB n b hb E p hp (g phi) (g psi))
  linearZ inner_exterior_form_isometry.
by [].
Qed.

(** Source for [hodge_unit_volume_dual]: Federer 1.7.8,
    p. 34, supporting identification of the top covector in the
    fourth identity: gamma(E) pairs to one with a unit E. *)
Lemma hodge_unit_volume_dual (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (E : exterior_power V n) (hE : exterior_norm h2 hB E = 1) :
  pairing E (inner_exterior_form h2 hB E) = 1.
Proof.
change (exterior_inner_form h2 hB E E = 1).
by rewrite -exterior_norm_square hE expr1n.
Qed.
