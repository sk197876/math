(** Federer (1969), 1.7.2, pp. 28-29: the inner product on one-forms is
    specified by making the polarity orthogonal. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerPolarity AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_dual_inner_product]: Federer 1.7.2, p. 28,
    abstract specification: an inner product on one-covectors which
    makes the given polarity an orthogonal map. *)
Record is_dual_inner_product (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (D : A_m V R^o 1 -> A_m V R^o 1 -> R) : Prop := {
  dual_inner_product_laws : is_inner_product D;
  dual_inner_product_polarity : forall x y,
    D (inner_polarity hB x) (inner_polarity hB y) = B x y
}.

(** Source for [dual_inner_product_unique]: Federer 1.7.2, p. 28,
    uniqueness of the induced inner product when polarity is onto.
    The onto hypothesis will be proved from finite dimension. *)
Lemma dual_inner_product_unique (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (D E : A_m V R^o 1 -> A_m V R^o 1 -> R) :
    (forall a, exists x, inner_polarity hB x = a) ->
    is_dual_inner_product hB D -> is_dual_inner_product hB E ->
    forall a b, D a b = E a b.
Proof.
move=> hs hD hE a b; have [x <-] := hs a; have [y <-] := hs b.
by rewrite (dual_inner_product_polarity hD) (dual_inner_product_polarity hE).
Qed.
