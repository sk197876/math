(** Federer (1969), 1.7.5, p. 32: normalising the factors of a nonzero
    simple multivector. No finite-dimensional ambient basis is needed for
    this consequence of Gram-Schmidt. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies OrthonormalisationUP
  FiniteIndependence GramSchmidt GramSchmidtExteriorFactor ExteriorHadamardBound
  AssociatedSubspace SimpleElementary ExteriorGrading FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simple_orthonormal_factor]: Federer 1.7.5,
    p. 32, every nonzero simple m-vector is a nonzero scalar
    times a product of m orthonormal vectors, including m=0. *)
Theorem simple_orthonormal_factor (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (x : exterior_power V m) : x != 0 -> simple x ->
  exists (e : 'I_m -> V) (c : R), orthonormal_family B e /\ c != 0 /\
    x = c *: e_lambda e (ord_tuple m).
Proof.
move=> hx [t ht]; rewrite tuple_product in ht.
have hu : finite_independent (tnth t).
  apply: exterior_product_nonzero_independent; by rewrite -ht.
have [e he] := @gram_schmidt_exists R V B hB m (tnth t) hu.
pose c := foldr ( *%R) 1 [seq B (tnth t i) (e i) | i <- enum 'I_m].
have hc : x = c *: e_lambda e (ord_tuple m).
  rewrite ht; exact: (@gram_schmidt_exterior_factor R h2 V B hB m (tnth t) e hu he).
exists e, c; split; first exact: orthonormalisation_orthonormal he.
split=> //; apply/eqP=> hz; by rewrite hc hz scale0r eqxx in hx.
Qed.
