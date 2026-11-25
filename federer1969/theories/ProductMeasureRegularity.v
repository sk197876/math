(** Federer (1969), 2.6.2(1), pp. 115–117: the Cartesian product measure is
    regular. Measurable rectangle covers and countable-intersection
    attainment give a measurable hull of equal measure. We reuse the
    attainment proof from 2.1.5 rather than repeating it for this particular
    measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureCountableClosure RegularMeasureUP
  MeasureRegularisationUP MeasureRegularisationAttainment ProductMeasureCoverUP ProductMeasure ProductRectangleMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.

(** Source for [product_measure_is_regular]: direct assertion Federer
    2.6.2(1), pp. 115–117 Every arbitrary set has a measurable superset with
    the same product measure, without any countable- measurability
    assumption on the factors or on the test set. *)
Theorem product_measure_is_regular (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  is_regular_measure (product_measure ha hb).
Proof.
pose nu := product_measure ha hb; have hm := product_measure_is_measure ha hb.
have hcov := product_measure_cover_specification ha hb.
have hr : is_measure_regularisation nu nu.
  constructor.
  - move=> A B hAB _; exact: (@measure_mono R (X * Y)%type nu hm A B hAB).
  - move=> A c hc; apply: (product_cover_greatest hcov)=> G hG hrect hcover.
    pose U := \bigcup_(p in G) (p.1 `*` p.2).
    have hU : measure_measurable nu U.
      apply: (@measure_measurable_countable_union R (X * Y)%type
        [the choiceType of (set X * set Y)%type] nu hm G (fun p => p.1 `*` p.2) hG).
      move=> p hp; exact (@product_measure_rectangle_measurable R X Y alpha beta ha hb p.1 p.2 (hrect p hp).1 (hrect p hp).2).
    apply: le_trans (hc U hcover hU) _.
    apply: (product_cover_lower hcov hG hrect)=> x hx; exact: hx.
move=> A; exact: (@measure_regularisation_attained R (X * Y)%type nu nu hm hr A).
Qed.
