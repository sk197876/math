(** Federer (1969), 1.7.5, p. 33: the inner product on m-covectors is
    characterised by requiring gamma_m to be orthogonal. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerExterior ExteriorGrading AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_exterior_covector_inner_product]: Federer
    1.7.5, p. 33, an inner product on m-covectors making gamma_m
    orthogonal. This abstract specification does not select an inverse
    or coordinates. Existence will use finite dimension. *)
Record is_exterior_covector_inner_product (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) m
    (D : A_m V R^o m -> A_m V R^o m -> R) : Prop := {
  exterior_covector_inner_laws : is_inner_product D;
  exterior_covector_inner_isometry : forall x y : exterior_power V m,
    D (inner_exterior_form h2 hB x) (inner_exterior_form h2 hB y) =
      exterior_inner_form h2 hB x y
}.

(** Source for [exterior_covector_inner_unique]: Federer
    1.7.5, p. 33, the isomorphism gamma_m determines the
    inner product on covectors uniquely. Surjectivity is explicit
    here and is supplied by finite dimension. *)
Theorem exterior_covector_inner_unique (R : realFieldType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) m
    (D E : A_m V R^o m -> A_m V R^o m -> R) :
  (forall a : A_m V R^o m, exists x, inner_exterior_form h2 hB x = a) ->
  is_exterior_covector_inner_product h2 hB D ->
  is_exterior_covector_inner_product h2 hB E -> forall a b, D a b = E a b.
Proof.
move=> hs hD hE a b; have [x <-] := hs a; have [y <-] := hs b.
by rewrite (exterior_covector_inner_isometry hD) (exterior_covector_inner_isometry hE).
Qed.
