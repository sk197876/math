(** Federer (1969), 4.1.5, p. 349: the original
    variation gauge on positive compact continuous scalar
    tests is the supremum of S(phi) under the pointwise norm
    bound. This is a scalar-test gauge, not a definition of
    a Borel measure for an arbitrary distribution. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distribution_variation_values]: the original
    real set inside the first displayed supremum of Federer
    4.1.5, p. 349. The evaluation map will be the actual test
    values, restricted to the original open domain. *)
Definition distribution_variation_values (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _))
    (S:Hom E R^o) (f:X->R):set R:=
  [set a|exists phi:E,(forall x,NY (value phi x)<=f x) /\ S phi=a].

(** Source for [is_distribution_variation_value]: independent
    least-upper-bound laws for the value ||S||(f) in Federer
    4.1.5, p. 349. Existence and opaque choice are separate.
    Only positive compact continuous f are the book's gauge
    domain; general positive majorants may also be compared. *)
Definition is_distribution_variation_value (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _))
    (S:Hom E R^o) (f:X->R) (c: \bar R):Prop:=
  is_extended_supremum (distribution_variation_values NY value S f) c.

(** Source for [distribution_variation_value_unique]: the
    original supremum value is unique, as required by the
    definition in Federer 4.1.5, p. 349, including infinity. *)
Lemma distribution_variation_value_unique (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (E:lmodType R)
    (value:Hom E (GRing.Lmodule.clone R (X->Y) _))
    (S:Hom E R^o) (f:X->R) c d:
  is_distribution_variation_value NY value S f c ->
  is_distribution_variation_value NY value S f d ->c=d.
Proof. exact:extended_supremum_unique. Qed.
