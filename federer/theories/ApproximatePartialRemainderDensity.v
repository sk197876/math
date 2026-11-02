(** Federer (1969), 3.1.4, pp. 214–215: the bad scalar
    increments T have density zero when the approximate partial exists.
    This supplies the exhaustion A_i=union_p B(i,j,p). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric RealNormUP RealMetricBackground EuclideanOneCoordinate
  EuclideanLebesgueDimensions EuclideanApproximateContext CenteredBallRelations
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialProductSections MeasureSetDensity MeasureApproximateLimitUP LocalZeroDensity
  ApproximatePartialDerivativeUP ApproximatePartialOrderGraphs CoordinateDifferenceQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [approximate_partial_remainder_density_zero]: the
    first exhaustion asserted in Federer 3.1.4, p. 215, from
    the definition of T on p. 214 and the approximate quotient
    in 3.1.2, p. 212. Radius restriction is applied afterwards. *)
Theorem approximate_partial_remainder_density_zero (R : realType) m
    (A : set (R_n R m)) (f : R_n R m -> R^o) a (i : 'I_m) c e :
  has_approximate_partial_derivative (scalar_absolute_value_norm R) A f a i c ->
  0<e ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R 1)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R 1)])
    [set t | e*`|euclidean_one_project t|<
      `|f (a+euclidean_one_project t*:(@coordinate_basis R m i))-f a-euclidean_one_project t*c|])
    (0 : inner_metric_space (@euclidean_inner_productP R 1)) 0%E.
Proof.
move=> hpartial he.
pose E := inner_metric_space (@euclidean_inner_productP R 1).
pose F := partial_function_source_restrict A (partial_function_total f).
pose Q := partial_product_vertical_section (euclidean_joint_coordinate_quotient i F) a.
have hlim := (approximate_partial_real_section_limit_iff i A f a c).1 hpartial.
pose U := [set z : real_line_metric R | `|c-z|<e].
have hU : nbhs (c : real_line_metric R) U.
  apply: (metricType_numDomainType.nbhs_mdistP (c : real_line_metric R) U).2.
  by exists e.
have hd := @hlim.2 U hU.
apply: (@local_zero_density_mono R [the metricType R of E]
  (@euclidean_lebesgue_measure R 1)
  (@centered_closed_ball_relation R [the metricType R of E])
  _ (~` partial_function_preimage Q U) setT 0 (euclidean_approximate_context R 1)
  openT Logic.I _ hd)=> t _ hbad [z [hz hgood]].
have [ht [u [v [[_ hu] [[_ hv] hq]]]]] :=
  (euclidean_joint_coordinate_quotient_graph i F a t z).1 hz.
change (f (a+euclidean_one_project t*:(@coordinate_basis R m i))=u) in hu.
change (f a=v) in hv.
have hid : f (a+euclidean_one_project t*:(@coordinate_basis R m i))-f a-
    euclidean_one_project t*c=euclidean_one_project t*(z-c).
  by rewrite hq -hu -hv mulrBr mulrA mulfV // mul1r.
have hbound : `|f (a+euclidean_one_project t*:(@coordinate_basis R m i))-f a-
    euclidean_one_project t*c|<e*`|euclidean_one_project t|.
  rewrite hid normrM mulrC ltr_pM2r ?normr_gt0 //.
  by rewrite distrC; exact hgood.
by have := lt_trans hbad hbound; rewrite ltxx.
Qed.
