(** Federer (1969), 1.7.3, p. 30: orthogonal-injection factorisation of a
    linear map with finite-dimensional source. Target capacity is an
    independent family of source dimension, so an infinite-dimensional
    target is allowed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  OrthonormalFamilies FiniteIndependence LinearBasis OrthogonalImageBasis
  PolarFactorisationUP PolarInjectionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [polar_injection_prescribed_basis]: Federer
    1.7.3, p. 30, both displayed basis prescriptions and h composed
    with g=f, for any orthonormal basis with orthogonal images. *)
Theorem polar_injection_prescribed_basis (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    (u : 'I_n -> U) (hu : finite_independent u) (f : {linear V -> U}) :
    (forall i j, i != j -> C (f (e i)) (f (e j)) = 0) ->
    exists (g : {linear V -> V}) (h : {linear V -> U}),
      is_injection_factorisation B C f g h /\
      (forall i, g (e i) = inner_norm hC (f (e i)) *: e i) /\
      (forall i, f (e i) != 0 -> h (e i) = inner_normalize hC (f (e i))).
Proof. exact: (@PolarInjection.exists_factors R V U B C hB hC n e he ho u hu f). Qed.

(** Source for [polar_injection_factorisation_exists]: Federer
    1.7.3, p. 30, if dim V is finite and dim V is at most dim U,
    then f=h composed with g for symmetric g and orthogonal injection h.
    An independent n-family in U states exactly the required lower
    bound on its dimension, including infinite-dimensional U. *)
Theorem polar_injection_factorisation_exists (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b)
    (u : 'I_n -> U) (hu : finite_independent u) (f : {linear V -> U}) :
    exists (g : {linear V -> V}) (h : {linear V -> U}),
      is_injection_factorisation B C f g h.
Proof.
have [e [he [ho hfo]]] := @orthonormal_orthogonal_image_basis R V U B C hB hC f n b hb.
have [g [h [hgh _]]] := @polar_injection_prescribed_basis R V U B C hB hC
  n e he ho u hu f hfo.
by exists g, h.
Qed.
