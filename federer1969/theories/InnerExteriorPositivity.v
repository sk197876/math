(** Federer (1969), 1.7.5, p. 32: the induced bilinear function is an inner
    product, also in arbitrary dimension. Finite-support reduction allows
    the coordinate-square proof without choosing a basis of the entire
    ambient space. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductRestriction InnerExterior
  InnerExteriorBasis InnerExteriorNaturality ExteriorPairReduction
  LinearBasis GramSchmidt OrthonormalisationUP OrthonormalFamilies
  ModuleQuotient SubspaceCarrier FiniteSpanSpace FiniteIndependence
  ExteriorGrading ExteriorMaps ExteriorSubspaceReduction OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_inner_product_finite_basis]: Federer
    1.7.5, p. 32, finite-dimensional positivity, starting with
    any basis and passing to an orthonormal basis as in the book. *)
Lemma exterior_inner_product_finite_basis (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m :
  is_inner_product (@exterior_inner_form R h2 V B hB m).
Proof.
have [d [hd hdo]] := @orthonormal_basis_exists R V B hB n e he.
exact: (@finite_exterior_inner_product R h2 V B hB n d
  (orthonormalisation_orthonormal hdo) hd m).
Qed.

(** Source for [exterior_inner_symmetric]: Federer 1.7.5,
    pp. 31-32, symmetry of the induced form. Here it follows
    by applying the book's coordinate formula in a common finite
    subspace carrying both vectors; this avoids a global basis. *)
Theorem exterior_inner_symmetric (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (x y : exterior_power V m) :
  exterior_inner_form h2 hB x y = exterior_inner_form h2 hB y x.
Proof.
have [n [e [he [a [b [ha hb]]]]]] := exterior_pair_finite_reduction x y.
pose S := finite_span_subspace e.
pose C := @restricted_inner_product R V B S.
have hC := @restricted_inner_productP R V B hB S.
have hi : is_orthogonal_map C B (subspace_inclusion S) by [].
have hE := @exterior_inner_product_finite_basis R h2 (finite_span_vect he)
  C hC n (finite_span_basis e) (finite_span_basisP he) m.
rewrite -ha -hb !(@exterior_inner_orthogonal_natural R h2
  (finite_span_vect he) V C B hC hB (subspace_inclusion S) hi).
exact (@inner_symmetric R (exterior_power (finite_span_vect he) m)
  _ hE a b).
Qed.

(** Source for [exterior_inner_positive]: Federer 1.7.5,
    p. 32, xi dot xi is positive exactly when xi is nonzero.
    The proof is the finite sum of coordinate squares after
    finite-support reduction, with no ambient dimension restriction. *)
Theorem exterior_inner_positive (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (x : exterior_power V m) :
  (0 < exterior_inner_form h2 hB x x) = (x != 0).
Proof.
have [n [e [he [a [b [ha hb]]]]]] := exterior_pair_finite_reduction x x.
pose S := finite_span_subspace e.
pose C := @restricted_inner_product R V B S.
have hC := @restricted_inner_productP R V B hB S.
have hi : is_orthogonal_map C B (subspace_inclusion S) by [].
have hE := @exterior_inner_product_finite_basis R h2 (finite_span_vect he)
  C hC n (finite_span_basis e) (finite_span_basisP he) m.
rewrite -ha (@exterior_inner_orthogonal_natural R h2
  (finite_span_vect he) V C B hC hB (subspace_inclusion S) hi) (inner_positive hE).
have hin := @exterior_power_subspace_injective R V S m.
by rewrite -(linear0 (exterior_power_map (subspace_inclusion S) m)) (inj_eq hin).
Qed.

(** Source for [exterior_inner_productP]: Federer 1.7.5,
    p. 32, the induced function is an inner product on every
    exterior power, in finite or infinite ambient dimension. *)
Theorem exterior_inner_productP (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) m :
  is_inner_product (@exterior_inner_form R h2 V B hB m).
Proof.
constructor.
- exact: exterior_inner_form_bilinear.
- exact: exterior_inner_symmetric.
- exact: exterior_inner_positive.
Qed.
