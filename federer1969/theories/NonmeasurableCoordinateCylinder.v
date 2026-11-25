(** Federer (1969), 3.2.7, p. 246,
    second example: a nonmeasurable scalar characteristic
    function remains nonmeasurable after pullback to the
    first coordinate of the plane. Expand the standard
    Fubini argument using the project's 2.6.5 product. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanCoordinateSplit EuclideanHeadSectionIntegral EuclideanNoncenteredVitali MetricClosedBalls
  RealMetricBackground ExtendedRealOrderTopology CharacteristicFunctionUP PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureIntegralUP PositiveCharacteristicMeasurability ProductSections LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_first_coordinate_cylinder_measurable]:
    supporting nonmeasurability in the second example
    of Federer 3.2.7, p. 246. A measurable
    full cylinder would make its characteristic scalar
    base measurable, by the positive full-section mass
    and the proved first-coordinate Fubini identity. *)
Lemma euclidean_first_coordinate_cylinder_measurable (R:realType)
    (B:set (real_line_metric R)) (c:R->R):
  is_characteristic_function B c ->
  measure_measurable (@euclidean_lebesgue_measure R 2)
    [set x:inner_metric_space (@euclidean_inner_productP R 2)|B (x ord0)] ->
  measure_measurable (@lebesgue_scalar_measure R) B.
Proof.
move=>hc hC.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose C:=[set x:inner_metric_space (@euclidean_inner_productP R 2)|B (x ord0)].
pose A:=(@euclidean_join R 1) @^-1` C.
pose nu:=@euclidean_lebesgue_measure R 1.
have hn:=euclidean_lebesgue_is_measure R 1.
have hPositive:(0%E<nu setT)%E.
  have hp:=@euclidean_closed_ball_positive R 1 (0%R:X) 1 (@ltr01 R).
  exact (lt_le_trans hp (measure_mono hn (subsetT _))).
have hSec y:nu (product_horizontal_section A y)=(nu setT*(c y)%:E)%E.
  case:(pselect (B y))=>hy.
  - have he:product_horizontal_section A y=setT.
      apply/seteqP; split=>u _; first exact I.
      change (B ((@euclidean_join R 1 (u,y)) ord0)); by rewrite euclidean_join_head.
    by rewrite he (characteristic_on_set hc hy) mule1.
  - have he:product_horizontal_section A y=set0.
      apply/seteqP; split=>u; last by case.
      change (B ((@euclidean_join R 1 (u,y)) ord0) -> False).
      by rewrite euclidean_join_head.
    have hEmpty:nu set0=0%E:=measure_empty hn.
    by rewrite he hEmpty (characteristic_off_set hc hy) mule0.
have hInt:=@euclidean_head_section_integral R 1 C hC.
have hEq:(fun y:R=>nu (product_horizontal_section A y))=
    (fun y:R=>(nu setT*(c y)%:E)%E) by apply:funext=>y; exact:hSec.
change (is_measure_integral (@lebesgue_scalar_measure R)
  (partial_function_total (fun y:R=>nu (product_horizontal_section A y)))
  (euclidean_lebesgue_measure 2 C)) in hInt.
rewrite hEq in hInt.
exact (positive_characteristic_measurable_set hc hPositive hInt.1).
Qed.
