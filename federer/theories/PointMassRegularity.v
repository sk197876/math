(** Supporting empty-product convention for Federer (1969), 2.6.5, pp.
    119–120: the zero-dimensional Euclidean space carries unit mass at its
    sole point. This convention extends the printed positive-factor
    construction; it is not stated as a separate claim by Federer. The
    point-mass definition is already used in 2.5.15, p. 108. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure PointMassMeasure
  BorelRegularMeasureUP TopologicalBorel CountablyMeasurableUP CountablyMeasurableBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [point_mass_every_set_measurable]: supporting
    measurability of the unit point mass for the empty product
    convention in Federer 2.6.5, pp. 119–120, from
    the measurable-set definition of 2.1.2, p. 54. *)
Lemma point_mass_every_set_measurable (R : realType) (X : choiceType) (x0 : X) (A : set X) :
  measure_measurable (point_mass R x0) A.
Proof.
move=> T; case: (pselect (T x0))=> hT; case: (pselect (A x0))=> hA.
- rewrite (point_mass_in R hT) (@point_mass_in R X x0 (T `&` A) (conj hT hA)) point_mass_out ?adde0 //.
  by move=> [_ hn]; exact: hn hA.
- rewrite (point_mass_in R hT) (@point_mass_in R X x0 (T `\` A) (conj hT hA)) point_mass_out ?add0e //.
  by move=> [_ ha]; exact: hA ha.
- rewrite (point_mass_out R hT) !point_mass_out ?add0e //; by move=> [ht _]; exact: hT ht.
- rewrite (point_mass_out R hT) !point_mass_out ?add0e //; by move=> [ht _]; exact: hT ht.
Qed.

(** Source for [point_mass_borel_regular]: supporting Borel
    regularity of the empty Euclidean product in Federer
    2.6.5, p. 120. More generally, a point mass is
    Borel regular whenever its singleton is closed. *)
Lemma point_mass_borel_regular (R : realType) (X : topologicalType) (x0 : X) :
  closed [set x0] -> is_borel_regular_measure (point_mass R x0).
Proof.
move=> hx; constructor.
- move=> U _; exact: point_mass_every_set_measurable.
- move=> A; case: (pselect (A x0))=> hA.
  + exists setT; split; first by move=> x _.
    split; first exact: open_borel_set openT.
    by rewrite (point_mass_in R hA) (@point_mass_in R X x0 setT Logic.I).
  + exists (~` [set x0]); split.
    * move=> x hax he; have heq : x = x0 := he.
      apply: hA; by rewrite -heq.
    * split; first exact: borel_set_complement (closed_borel_set hx).
      by rewrite (point_mass_out R hA) point_mass_out //; move=> h; exact: h (erefl _).
Qed.

(** Source for [point_mass_countably_measurable]: finite
    total mass for the empty-product convention supporting
    Federer 2.6.5, pp. 119–120. *)
Lemma point_mass_countably_measurable (R : realType) (X : choiceType) (x0 : X) :
  measure_countably_measurable (point_mass R x0) setT.
Proof.
apply: finite_measurable_set_countably_measurable; first exact: point_mass_every_set_measurable.
by rewrite (@point_mass_in R X x0 setT Logic.I) ltry.
Qed.
