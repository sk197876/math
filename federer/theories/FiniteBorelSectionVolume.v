(** Supporting Federer (1969), 2.10.46, p. 204: horizontal section volumes
    of a Borel product set are Borel functions when the first measure is
    finite and both spaces have countable bases. Rectangle induction uses
    the proved Dynkin criterion; finite subtraction and increasing
    continuity are 2.1.2–2.1.3, pp. 54–55. Baire pointwise closure is
    2.2.15, pp. 70–71. This proves actual Borel level sets, not merely
    measurability for a completion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CountableOpenBaseUP TopologicalBorel
  BorelRectangleDynkin FiniteSectionBaireFamily FiniteMeasureRealLaws
  MeasureUP MeasureBasic MeasureSplit ProductSections SwitchedRectangleSections
  BaireFunctions BaireRealAlgebra BorelCharacteristicBaire CharacteristicFunctionUP
  BaireBorel BorelFunctionBasic CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_borel_horizontal_section_baire]:
    supporting Baire section-volume function for 2.10.46,
    p. 204, using Borel generation 2.2.1 and the
    Baire algebra and limit laws of 2.2.15, pp. 70–71.
    First-factor Borel measurability and finite total mass are
    explicit; no regularity beyond those hypotheses is needed. *)
Theorem finite_borel_horizontal_section_baire (R : realType) (X : topologicalType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (U : nat -> set X) (V : nat -> set Y) :
  is_countable_open_base U -> is_countable_open_base V -> mu setT< +oo ->
  (forall A, borel_set A -> measure_measurable mu A) -> forall S, borel_set S ->
  (forall y, measure_measurable mu (product_horizontal_section S y)) /\
  @is_baire_function R Y [the metricType R of real_line_metric R]
    (fun y=>fine (mu (product_horizontal_section S y))).
Proof.
move=> hU hV ht hmb.
apply: (@borel_product_dynkin_criterion X Y U V _ hU hV
  (@finite_horizontal_sections_baire_dynkin R X Y mu hm ht)).
move=> A B hA hB; split.
- move=> y; case: (pselect (B y))=> hy.
  + rewrite (rectangle_horizontal_section_on A hy); exact: hmb.
  + rewrite (rectangle_horizontal_section_off A hy); exact: measure_measurable_empty hm.
- have [s [hs hsb]] := @borel_set_has_baire_characteristic R Y B hB.
  have he : (fun y=>fine (mu (product_horizontal_section (A `*` B) y)))=
      (fun y=>(fine (mu A)*s y)%R).
    apply: funext=> y; case: (pselect (B y))=> hy.
    + by rewrite (rectangle_horizontal_section_on A hy) (characteristic_on_set hs hy) mulr1.
    + by rewrite (rectangle_horizontal_section_off A hy) (measure_empty hm)
        (characteristic_off_set hs hy) mulr0.
  rewrite he; exact: baire_real_scale hsb.
Qed.

(** Source for [finite_borel_horizontal_section_level]:
    supporting Borel superlevel set for 2.10.46, p. 204.
    The real section-volume function just proved is Borel
    by 2.2.15, p. 70; take its closed-ray preimage
    using 2.2.14, p. 70. *)
Theorem finite_borel_horizontal_section_level (R : realType) (X : topologicalType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (U : nat -> set X) (V : nat -> set Y) (S : set (X*Y)) (c : R) :
  is_countable_open_base U -> is_countable_open_base V -> mu setT< +oo ->
  (forall A, borel_set A -> measure_measurable mu A) -> borel_set S ->
  borel_set [set y | c%:E<=mu (product_horizontal_section S y)].
Proof.
move=> hU hV ht hmb hS.
have hb := (finite_borel_horizontal_section_baire hm hU hV ht hmb hS).2.
have he : [set y | c%:E<=mu (product_horizontal_section S y)]=
    (fun y=>(fine (mu (product_horizontal_section S y)) : real_line_metric R)) @^-1` [set r | (c<=r)%R].
  apply/seteqP; split=> y; rewrite /= (finite_total_measure_value hm ht _) lee_fin; by [].
rewrite he; apply (@borel_function_preimage Y [the topologicalType of real_line_metric R]
  (fun y=>fine (mu (product_horizontal_section S y))) (baire_function_borel hb) [set r | (c<=r)%R]).
apply: closed_borel_set.
exact: (@order_closed_upper_ray_closed _ [the orderTopologicalType _ of R^o] c).
Qed.
