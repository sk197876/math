(** Supporting empty-block convention for the Euclidean product identity of
    Federer (1969), 2.6.5, p. 120. A singleton factor with unit mass is
    neutral for a regular measure. Regularity is retained because Federer's
    product uses measurable rectangle covers; it cannot be silently dropped
    for an arbitrary outer measure. Dimension zero is an explicit extension
    of the printed positive-dimensional definition. Source context:
    EuclideanLebesgueDimensions.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasurePushforward
  RegularMeasureUP PointMassMeasure PointMassRegularity ProductMeasure MeasureBijectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [singleton_product_measure]: supporting neutral
    singleton factor for the zero-dimensional extension of
    Federer 2.6.5, p. 120. The equality is for every
    subset, using an equal-measure measurable hull in the
    non-singleton factor. *)
Theorem singleton_product_measure (R : realType) (X Y : choiceType) (x0 : X)
    (beta : set Y -> \bar R) (hb : is_measure beta) :
  (forall x : X, x = x0) -> is_regular_measure beta ->
  measure_pushforward (fun y => (x0,y)) beta = product_measure (point_mass_is_measure R x0) hb.
Proof.
move=> hx hr; apply: funext=> S; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: product_measure_greatest; first exact: measure_pushforward_is_measure hb.
  move=> A B _ _; rewrite /measure_pushforward.
  case: (pselect (A x0))=> hA.
  + rewrite (point_mass_in R hA) mul1e.
    apply: (@measure_mono R Y beta hb [set y | (A `*` B) (x0,y)] B).
    by move=> y [_ hy].
  + rewrite (point_mass_out R hA) mul0e.
    have he : [set y | (A `*` B) (x0,y)] = set0.
      apply/seteqP; split=> y //; move=> [hy _]; exact: False_ind _ (hA hy).
    change (beta [set y | (A `*` B) (x0,y)] <= 0).
    by rewrite he (measure_empty hb).
- have [B [hSB [hB he]]] := hr [set y | S (x0,y)].
  have hs : S `<=` setT `*` B.
    move=> [x y] hxy; split=> //; apply: hSB; by rewrite -(hx x).
  have hmono := measure_mono (product_measure_is_measure (point_mass_is_measure R x0) hb) hs.
  have hrect := product_measure_rectangle_bound (point_mass_is_measure R x0) hb
    (point_mass_every_set_measurable R x0 setT) hB.
  have hone : point_mass R x0 setT = 1 := @point_mass_in R X x0 setT Logic.I.
  rewrite hone mul1e in hrect.
  rewrite /measure_pushforward he; exact: le_trans hmono hrect.
Qed.

(** Source for [singleton_product_bijection]: supporting
    canonical unit-factor identification for the zero-dimensional
    extension of Federer 2.6.5, p. 120. *)
Lemma singleton_product_bijection (R : realType) (X Y : choiceType) (x0 : X)
    (beta : set Y -> \bar R) (hb : is_measure beta) :
  (forall x : X, x = x0) -> is_regular_measure beta ->
  is_measure_bijection beta (product_measure (point_mass_is_measure R x0) hb)
    (fun y => (x0,y)) (fun p => p.2).
Proof.
move=> hx hr; constructor=> //.
- by move=> [x y]; rewrite (hx x).
- exact: singleton_product_measure hx hr.
Qed.
