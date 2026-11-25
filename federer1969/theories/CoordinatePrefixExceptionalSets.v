(** Federer (1969), 3.1.4, p. 215: the exceptional
    prefix/scalar pairs whose cylinders contain S_i. Measurability
    is proved on the conull set of qualified base points. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanLebesgueDimensions EuclideanPrefixTranslation
  EuclideanPrefixCutoffs CoordinateSectionGoodBases PrefixCylinderAdapters
  EuclideanBlockCoordinates EuclideanBlockMeasurableFunctions EuclideanOneCoordinate
  EuclideanMetricProduct MetricCartesianProductUP EuclideanCoordinateStaircase
  ApproximateCoordinateExceptionalSets CoordinateRemainderSetMeasurable
  ScalarRemainderMeasurability RealMetricBackground PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages PartialFunctionPrecomposition MeasurableFunctionUP
  MeasurableGraphEquivalence ProductMeasure ProductFunctionMeasurability
  ProductRectangleValue ProductSections MeasureUP MeasureSplit MeasureFiniteClosure
  MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section PrefixExceptions.
Variable R : realType.
Variable m : nat.
Variable i : 'I_m.
Local Notation E n := (inner_metric_space (@euclidean_inner_productP R n)).
Variables f g : E m -> R^o.
Variable a : E m.
Variable e : R.

(** Source for [coordinate_prefix_remainder_set]: the scalar
    remainder alternative in S_i, Federer 3.1.4, p. 215,
    written on the prefix/scalar product. *)
Definition coordinate_prefix_remainder_set : set (E i*E 1) :=
  [set ut | e*`|euclidean_one_project ut.2|<
    `|f (@euclidean_prefix_translation R m (i+1) a (euclidean_block_join ut))-
      f (@euclidean_prefix_translation R m i a ut.1)-
      euclidean_one_project ut.2*g (@euclidean_prefix_translation R m i a ut.1)|].

(** Source for [coordinate_prefix_remainder_as_section]:
    the scalar T section based at a plus the earlier coordinate
    increments, Federer 3.1.4, p. 215. *)
Lemma coordinate_prefix_remainder_as_section u t :
  coordinate_prefix_remainder_set (u,t) <->
    coordinate_remainder_exception_set i f g e
      (@euclidean_prefix_translation R m i a u,t).
Proof.
rewrite /coordinate_prefix_remainder_set /coordinate_remainder_exception_set /=.
by rewrite euclidean_prefix_translation_step.
Qed.

(** Source for [coordinate_prefix_remainder_measurable]:
    the measurable scalar remainder section needed for the
    Fubini estimate in Federer 3.1.4, p. 215. *)
Theorem coordinate_prefix_remainder_measurable B :
  coordinate_section_good_bases i f g B a ->
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R i)
    (euclidean_lebesgue_is_measure R 1)) coordinate_prefix_remainder_set.
Proof.
move=> [h0 [h1 [hg _]]].
pose ha := euclidean_lebesgue_is_measure R i.
pose hb := euclidean_lebesgue_is_measure R 1.
pose mu := product_measure ha hb.
have h0t : is_measure_measurable_function (@euclidean_lebesgue_measure R i)
    (partial_function_total (fun u : E i=>
      (f (@euclidean_prefix_translation R m i a u) : real_line_metric R))).
  apply: (measurable_function_graph_equivalent _ h0)=> u z; by [].
have hgt : is_measure_measurable_function (@euclidean_lebesgue_measure R i)
    (partial_function_total (fun u : E i=>
      (g (@euclidean_prefix_translation R m i a u) : real_line_metric R))).
  apply: (measurable_function_graph_equivalent _ hg)=> u z; by [].
have hF0 := euclidean_block_join_measurable_precompose h1.
have hF : is_measure_measurable_function mu
    (partial_function_total (fun ut : E i*E 1=>
      (f (@euclidean_prefix_translation R m (i+1) a (euclidean_block_join ut)) :
        real_line_metric R))).
  apply: (measurable_function_graph_equivalent _ hF0)=> ut z; by [].
have hH := product_measurable_first_function ha hb h0t.
have hG := product_measurable_first_function ha hb hgt.
have ht0 : is_measure_measurable_function (@euclidean_lebesgue_measure R 1)
    (partial_function_total (fun t : E 1=>(euclidean_one_project t : real_line_metric R))).
  constructor.
  - rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hb.
  - move=> W hW; rewrite partial_function_total_preimage.
    apply: (borel_regular_open_measurable (euclidean_lebesgue_borel_regular R 1)).
    apply: open_comp hW=> t _; exact: euclidean_one_project_continuous.
have ht := product_measurable_second_function ha hb ht0.
exact (@measurable_scalar_remainder_comparison R [the choiceType of (E i*E 1)%type]
  mu (product_measure_is_measure ha hb) _ _ _ _ e hF hH ht hG).
Qed.

Variable B : set (E m).
Variable r : R.

(** Source for [coordinate_prefix_exception_product]: the
    two alternatives of S_i, Federer 3.1.4, p. 215,
    in a containing product of prefix and scalar radius balls.
    Z retains the erratum p. 4 correction for book p. 214 line 24. *)
Definition coordinate_prefix_exception_product : set (E i*E 1) :=
  (metric_closed_ball (0 : E i) r `*` metric_closed_ball (0 : E 1) r) `&`
  ((product_vertical_section (@prefix_slice_variation_exception R m i B g e) a
    `*` setT) `|` coordinate_prefix_remainder_set).

(** Source for [coordinate_prefix_exception_product_measurable]:
    joint measurability needed for Fubini in Federer 3.1.4,
    p. 215, at each base where the requisite slices are measurable. *)
Theorem coordinate_prefix_exception_product_measurable :
  coordinate_section_good_bases i f g B a ->
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R i)
    (euclidean_lebesgue_is_measure R 1)) coordinate_prefix_exception_product.
Proof.
move=> hgood.
pose ha := euclidean_lebesgue_is_measure R i.
pose hb := euclidean_lebesgue_is_measure R 1.
pose hm := product_measure_is_measure ha hb.
have hball n : measure_measurable (@euclidean_lebesgue_measure R n)
    (metric_closed_ball (0 : E n) r).
  apply: (borel_regular_borel_measurable (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_borel_regular R n)).
  apply: closed_borel_set; exact: metric_closed_ball_closed.
apply: (measure_measurable_intersection hm).
- exact: (product_measure_measurable_rectangle ha hb (hball i) (hball 1)).1.
- apply: (measure_measurable_union hm).
  + exact: (product_measure_measurable_rectangle ha hb
      (coordinate_good_base_variation_measurable e hgood)
      (measure_measurable_whole hb)).1.
  + exact: coordinate_prefix_remainder_measurable hgood.
Qed.

(** Source for [coordinate_staircase_exception_prefix_cover]:
    containing the coordinate exception in the product-cylinder
    estimate of Federer 3.1.4, p. 215. *)
Theorem coordinate_staircase_exception_prefix_cover
    (hi : (i<=m)%N) (hj : (i+1<=m)%N) h :
  coordinate_staircase_exception f (fun _=>g) a e i h ->
  metric_closed_ball (0 : E m) r h ->
  coordinate_prefix_exception_product
    (@euclidean_block_split R i 1 (euclidean_prefix_restriction hj h)).
Proof.
move=> hex hball.
rewrite (euclidean_prefix_restriction_step hi hj h).
split.
- split; first exact: euclidean_prefix_restriction_ball hball.
  have hp := euclidean_prefix_restriction_ball hj hball.
  have hz : @euclidean_block_split R i 1 0=(0,0).
    rewrite /euclidean_block_split; congr (_, _); apply/ffunP=> j; by rewrite !ffunE.
  have hs := (metric_product_second_nonexpanding
    (euclidean_blocks_are_metric_product R i 1)).2
    0 (euclidean_prefix_restriction hj h) Logic.I Logic.I.
  rewrite hz (euclidean_prefix_restriction_step hi hj h) /= mul1r in hs.
  exact: le_trans hs hp.
- case: hex=> [hrem|hvar].
  + right; apply: (coordinate_prefix_remainder_as_section _ _).2.
    rewrite /coordinate_remainder_exception_set /= euclidean_one_embedK
      /euclidean_prefix_translation euclidean_prefix_inclusion_restriction.
    exact hrem.
  + left; split; last exact Logic.I.
    right.
    rewrite /euclidean_prefix_translation euclidean_prefix_inclusion_restriction.
    exact hvar.
Qed.
End PrefixExceptions.
