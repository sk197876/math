(** Federer (1969), 1.7.8, p. 34: pairing preservation implies that the
    Hodge maps preserve inner products and norms. These supporting
    consequences are used in the later metric formulas of 1.7.11-1.7.13. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerExterior
  InnerExteriorIsomorphism ExteriorCovectorInner ExteriorNorm ExteriorGrading
  AlternatingCoordinates LinearBasis HodgeMaps HodgePairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Isometry.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Variable E : exterior_power V n.
Hypothesis hE : exterior_norm h2 hB E = 1.
Variable p : nat.
Hypothesis hp : (p <= n)%N.

(** Source for [hodge_vector_inner]: Federer 1.7.8,
    p. 34, supporting inner-product form of the simultaneous
    pairing identity, using the gamma diagram. *)
Theorem hodge_vector_inner (x y : exterior_power V p) :
  exterior_inner_form h2 hB (hodge_vector h2 hB E hp x) (hodge_vector h2 hB E hp y) =
    exterior_inner_form h2 hB x y.
Proof.
rewrite /exterior_inner_form -hodge_polarity_diagram.
exact: (@hodge_pairing R h2 V B hB n b hb E hE p hp x (inner_exterior_form h2 hB y)).
Qed.

(** Source for [hodge_vector_norm]: Federer 1.7.8,
    p. 34, supporting norm preservation; later used in 1.7.11,
    p. 36. It includes degree zero and top degree. *)
Theorem hodge_vector_norm (x : exterior_power V p) :
  exterior_norm h2 hB (hodge_vector h2 hB E hp x) = exterior_norm h2 hB x.
Proof.
apply: inner_norm_value; first exact: exterior_norm_nonnegative.
by rewrite exterior_norm_square hodge_vector_inner.
Qed.

(** Source for [hodge_covector_inner]: Federer 1.7.8,
    p. 34, supporting covector inner-product preservation,
    transferred through the polarity isometry. *)
Theorem hodge_covector_inner (phi psi : A_m V R^o p) :
  exterior_covector_inner h2 hB hb (hodge_covector h2 hB E hp phi)
    (hodge_covector h2 hB E hp psi) = exterior_covector_inner h2 hB hb phi psi.
Proof.
have [g [_ hgi]] := @inner_exterior_inverse_exists R h2 V B hB n b hb p.
by rewrite -(hgi phi) -(hgi psi) !hodge_polarity_diagram
  !inner_exterior_form_isometry hodge_vector_inner.
Qed.

(** Source for [hodge_covector_norm]: Federer 1.7.8,
    p. 34, supporting norm preservation for covectors. *)
Theorem hodge_covector_norm (phi : A_m V R^o p) :
  exterior_covector_norm h2 hB hb (hodge_covector h2 hB E hp phi) =
    exterior_covector_norm h2 hB hb phi.
Proof.
have [g [_ hgi]] := @inner_exterior_inverse_exists R h2 V B hB n b hb p.
by rewrite -(hgi phi) hodge_polarity_diagram !inner_exterior_form_norm hodge_vector_norm.
Qed.
End Isometry.
