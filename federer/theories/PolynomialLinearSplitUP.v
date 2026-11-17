(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: a field containing a full linear
    factorisation of an original polynomial. Independent
    factorisation laws precede the root adjunctions.
    Source: Bourbaki, Algebra II (1990), Chapter V,
    section 4, no. 2, Proposition 4, pp. V.21–22. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialEvaluationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_linear_polynomial_split]: the linear
    factorisation supplied by a containing field in
    Bourbaki (1990), Chapter V, section 4,
    no. 2, Proposition 4, pp. V.21–22;
    supporting 3.4.8(8), pp. 329–330. The
    original evaluation identity remains valid in
    every further field extension. *)
Record is_linear_polynomial_split (K:fieldType) (B:comNzRingType)
  (embed:{rmorphism K->B}) (variable P:B) d (L:fieldType)
  (phi:{rmorphism K->L}) (c:L) (roots:seq L):Prop:={
  (** Source for [linear_split_scalar_nonzero]: the
      original leading scalar is nonzero in
      the cited linear factorisation. *)
  linear_split_scalar_nonzero:c<>0;
  (** Source for [linear_split_root_count]: the
      linear factors, counted with multiplicity,
      number the original degree in the cited proposition. *)
  linear_split_root_count:size roots = d;
  (** Source for [linear_split_evaluation]: the exact
      product of original linear factors in
      the cited proposition, preserved under
      every further scalar extension. *)
  linear_split_evaluation:forall (Z:fieldType) (psi:{rmorphism L->Z})
    (chi:{rmorphism K->Z}) (z:Z) (E:{rmorphism B->Z}),
    (forall a:K,chi a = psi (phi a)) ->
    is_commutative_polynomial_evaluation embed variable chi z E ->
    E P = psi c*\prod_(r<-roots) (z-psi r)
}.
