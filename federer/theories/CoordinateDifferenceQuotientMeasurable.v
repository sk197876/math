(** Federer (1969), 3.1.4, p. 214, first paragraph of proof:
    the coordinate difference quotient is jointly Lebesgue measurable
    by 3.1.3(3) and the measurable scalar arithmetic of 2.3.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric ApproximateDifferentialAffine EuclideanLebesgueDimensions EuclideanNoncenteredVitali EuclideanBlockCoordinates
  EuclideanOneCoordinate EuclideanCoordinateLineMap EuclideanEpimorphismNull
  EuclideanBlockMeasurableFunctions CoordinateDifferenceQuotient RealMetricBackground
  RealReciprocalBorel PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  PartialFunctionPrecomposition MeasurableFunctionUP MeasurableRealArithmetic
  MeasurableTotalBasic MeasurableGraphEquivalence MeasurableConullSourceRestriction
  MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic
  ProductMeasure ProductRectangleValue
  BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_joint_coordinate_quotient_measurable]:
    the joint measurability used to apply 3.1.3(2) in Federer 3.1.4,
    p. 214. Surjectivity and the null zero-parameter cylinder are proved;
    proper conull function domains are retained. *)
Theorem euclidean_joint_coordinate_quotient_measurable (R : realType) n (i : 'I_n)
    (f : partial_function (inner_metric_space (@euclidean_inner_productP R n)) (real_line_metric R)) :
  is_measure_measurable_function (@euclidean_lebesgue_measure R n) f ->
  is_measure_measurable_function (product_measure (euclidean_lebesgue_is_measure R n)
    (euclidean_lebesgue_is_measure R 1)) (euclidean_joint_coordinate_quotient i f).
Proof.
move=> hf.
pose E k := inner_metric_space (@euclidean_inner_productP R k).
pose ha := euclidean_lebesgue_is_measure R n.
pose hb := euclidean_lebesgue_is_measure R 1.
pose mu := product_measure ha hb.
pose hm := product_measure_is_measure ha hb.
pose p := GRing.Linear.clone _ _ _ _ (@euclidean_coordinate_line_map R n i) _.
have hs0 := euclidean_epimorphism_measurable_precompose (p:=p)
  (@euclidean_coordinate_line_map_surjective R n i) hf.
have hs1 := euclidean_block_join_measurable_precompose hs0.
have hs : is_measure_measurable_function mu
    (partial_function_precompose (fun xt : E n*E 1=>xt.1+euclidean_one_project xt.2*:(@coordinate_basis R n i)) f).
  apply: (@measurable_function_graph_equivalent R _ [the topologicalType of real_line_metric R]
    _ _ _ _ hs1).
  move=> [x t] z.
  change (partial_function_graph f (euclidean_coordinate_line_map i (euclidean_block_join (x,t))) z <->
    partial_function_graph f (x+euclidean_one_project t*:(@coordinate_basis R n i)) z).
  by rewrite euclidean_coordinate_line_map_pair.
pose p0 := GRing.Linear.clone _ _ _ _ (@euclidean_coordinate_parameter_base R n) _.
have hb0 := euclidean_epimorphism_measurable_precompose (p:=p0)
  (@euclidean_coordinate_parameter_base_surjective R n) hf.
have hb1 := euclidean_block_join_measurable_precompose hb0.
have hbase : is_measure_measurable_function mu
    (partial_function_precompose (fun xt : E n*E 1=>xt.1) f).
  apply: (@measurable_function_graph_equivalent R _ [the topologicalType of real_line_metric R]
    _ _ _ _ hb1).
  move=> [x t] z.
  change (partial_function_graph f (euclidean_coordinate_parameter_base (euclidean_block_join (x,t))) z <-> partial_function_graph f x z).
  by rewrite /euclidean_coordinate_parameter_base euclidean_block_joinK.
have ht1 : is_measure_measurable_function (@euclidean_lebesgue_measure R 1)
    (partial_function_total (fun t : E 1=>(euclidean_one_project t : real_line_metric R))).
  constructor.
  - rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hb.
  - move=> U hU; rewrite partial_function_total_preimage.
    apply: (borel_regular_open_measurable (euclidean_lebesgue_borel_regular R 1)).
    apply: open_comp hU=> t _; exact: euclidean_one_project_continuous.
have ht : is_measure_measurable_function mu (partial_function_total
    (fun xt : E n*E 1=>(euclidean_one_project xt.2 : real_line_metric R))).
  constructor.
  - rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
  - move=> U hU; rewrite partial_function_total_preimage.
    have he : (fun xt : E n*E 1=>euclidean_one_project xt.2) @^-1` U=
        setT `*` ((@euclidean_one_project R) @^-1` U).
      apply/seteqP; split=> xt hxt; [by split|exact hxt.2].
    rewrite he; apply: (product_measure_measurable_rectangle ha hb (measure_measurable_whole ha) _).1.
    have hh := measurable_function_open_preimage ht1 hU.
    by rewrite partial_function_total_preimage in hh.
have hinv := @measurable_total_borel_postcomposition R _
  [the topologicalType of real_line_metric R] [the topologicalType of real_line_metric R]
  mu hm _ (fun t=>t^-1) ht (@real_reciprocal_borel R).
have hpunctured : measure_almost_everywhere mu [set xt : E n*E 1 | euclidean_one_project xt.2 != 0].
  have he : ~` [set xt : E n*E 1 | euclidean_one_project xt.2 != 0]=setT `*` [set (0 : E 1)].
    apply/seteqP; split.
    + move=> [x t] ht0; split; first exact Logic.I.
      have hp0 : euclidean_one_project t=0.
        case: (eqVneq (euclidean_one_project t) 0)=> [heq|hne]; first exact heq.
        exfalso; exact: ht0 hne.
      have htE := euclidean_one_projectK t; rewrite hp0 in htE.
      have he0 : euclidean_one_embed (0 : R)=(0 : E 1).
        by apply/ffunP=> j; rewrite /euclidean_one_embed !ffunE.
      by move: htE; rewrite he0=> ->.
    + move=> [x t] [_ ht0]; change (t=0) in ht0.
      by rewrite /= ht0 /euclidean_one_project ffunE eqxx.
  rewrite /measure_almost_everywhere he /mu product_measure_rectangle_value.
  - by rewrite (@positive_euclidean_singleton_null R 0 (0 : E 1)) mule0.
  - exact: measure_measurable_whole ha.
  - exact: (@measure_null_measurable R [the choiceType of E 1]
      (@euclidean_lebesgue_measure R 1) hb [set (0 : E 1)]
      (@positive_euclidean_singleton_null R 0 (0 : E 1))).
apply: (@measurable_conull_source_restriction R _ _ mu hm _ _ hpunctured).
apply: (@measurable_real_function_multiply R [the choiceType of (E n*E 1)%type] mu hm _ _ hinv).
exact: (@measurable_real_function_subtract R [the choiceType of (E n*E 1)%type] mu hm _ _ hs hbase).
Qed.
