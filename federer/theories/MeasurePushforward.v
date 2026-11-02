(** Federer (1969), 2.1.2, pp. 53-54. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureIndexedCover MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_pushforward]: Federer 2.1.2, p. 54, final
    definition: image measure evaluates a set by the measure of its inverse
    image. Federer uses a total function X to Y, as here *)
Definition measure_pushforward (R : realType) (I J : choiceType)
    (f : I -> J) (mu : set I -> \bar R) (B : set J) := mu (f @^-1` B).

(** Source for [measure_pushforward_is_measure]: Federer 2.1.2, p. 54, image
    measure is a measure over Y. *)
Lemma measure_pushforward_is_measure (R : realType) (I J : choiceType)
    (f : I -> J) (mu : set I -> \bar R) (hm : is_measure mu) :
  is_measure (measure_pushforward f mu).
Proof.
constructor; first by move=> A; exact: (@measure_nonnegative R I mu hm).
move=> A F hF hc; apply: (@measure_indexed_cover R I _ mu hm _ F _ hF).
move=> x hx; have [B hB hxB] := hc (f x) hx.
by exists B.
Qed.

(** Source for [measure_pushforward_restrictions_iff]: Federer 2.1.2, p. 54,
    final sentence: inverse-image measurability is equivalent to
    measurability for every restricted image measure. Here f is total as in
    Federer The equivalence itself uses only splitting laws. *)
Lemma measure_pushforward_restrictions_iff (R : realType)
    (I J : choiceType) (f : I -> J) (mu : set I -> \bar R) (B : set J) :
  measure_measurable mu (f @^-1` B) <->
  (forall A, measure_measurable (measure_pushforward f (measure_restrict mu A)) B).
Proof.
split.
- move=> h A T; rewrite /measure_pushforward /measure_restrict.
  rewrite (h (A `&` (f @^-1` T))).
  by rewrite !setDE !preimage_setI -preimage_setC !setIA.
- move=> h T; have ht := h T setT.
  by rewrite /measure_pushforward /measure_restrict preimage_setT
    setIT setTI setDE preimage_setI preimage_setT -preimage_setC setTI in ht.
Qed.
