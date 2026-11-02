(** Federer (1969), 3.1.4, p. 214, opening paragraph of proof:
    finite matching approximate upper and lower quotient limits specify
    the approximate partial derivative. The equality below uses the
    exact sealed graph introduced in 3.1.2 and retains the base domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanLebesgueDimensions EuclideanOneCoordinate RealMetricBackground
  RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialFunctionPrecomposition PartialFunctionPostcomposition PartialProductSections
  CoordinateDifferenceQuotient ApproximatePartialDerivativeUP ApproximatePartialDerivative
  ScalarApproximateTargetTopology ScalarEuclideanApproximateLimits
  EuclideanApproximateRealOrder ApproximateLimitGraphEquivalence
  MeasureApproximateLimitUP MeasureApproximateOrderLimits CenteredBallRelations
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ScalarPartial.
Variable R : realType.
Variable n : nat.
Variable i : 'I_n.
Variable A : set (R_n R n).
Variable f : R_n R n -> R^o.
Local Notation hN := (scalar_absolute_value_norm R).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R 1)).
Local Notation F := (partial_function_source_restrict A
  (partial_function_total (fun x=>(f x : real_line_metric R)))).
Local Notation Q a := (partial_product_vertical_section (euclidean_joint_coordinate_quotient i F) a).

(** Source for [approximate_partial_quotient_section_graph]: supporting
    scalar and Euclidean parameter identification for the displayed
    quotient in Federer 3.1.4, p. 214. The base-point hypothesis is the
    explicit condition needed to use f(a) in the printed formula. *)
Lemma approximate_partial_quotient_section_graph a : A a -> forall t y,
  partial_function_graph
    (partial_function_precompose (@euclidean_one_project R)
      (partial_function_postcompose (approximate_partial_quotient hN A f a i)
        (fun z=>(z : real_line_metric R)))) t y <->
  partial_function_graph (Q a) t y.
Proof.
move=> ha t y.
change (partial_function_graph
    (partial_function_precompose (@euclidean_one_project R)
      (partial_function_postcompose (approximate_partial_quotient hN A f a i)
        (fun z=>(z : real_line_metric R)))) t y <->
    partial_function_graph (euclidean_joint_coordinate_quotient i F) (a,t) y).
rewrite euclidean_joint_coordinate_quotient_graph.
split.
- move=> [v [[[ht hAt] hv] <-]]; split=> //.
  exists (f (a+euclidean_one_project t*:(@coordinate_basis R n i))), (f a).
  split; first by split.
  split; first by split.
  by rewrite -hv.
- move=> [ht [u [v [[hAt hu] [[_ hv] hy]]]]].
  exists y; split; last by [].
  split; first by split.
  change ((euclidean_one_project t)^-1*:(f (a+euclidean_one_project t*:(@coordinate_basis R n i))-f a)=y).
  by rewrite hy -hu -hv.
Qed.

(** Source for [approximate_partial_real_section_limit_iff]: the
    coordinate derivative exists with value c exactly when its jointly
    measurable quotient section has approximate limit c, supporting
    Federer 3.1.4, p. 214. The real and normed scalar topologies and the
    one-dimensional measure identification are proved compatible. *)
Lemma approximate_partial_real_section_limit_iff a c :
  has_approximate_partial_derivative hN A f a i c <->
  A a /\ is_measure_approximate_limit (@euclidean_lebesgue_measure R 1)
    (@centered_closed_ball_relation R [the metricType R of E]) (Q a) (0 : E) c.
Proof.
rewrite /has_approximate_partial_derivative scalar_norm_approximate_limit_iff
  scalar_euclidean_approximate_limit_iff.
have he0 : euclidean_one_embed (0 : real_line_metric R)=(0 : E).
  by apply/ffunP=> j; rewrite /euclidean_one_embed !ffunE.
rewrite he0; split; move=> [ha hl]; split=> //.
- apply: (@approximate_limit_graph_equivalent R [the metricType R of E]
    [the topologicalType of real_line_metric R] _ _ _ _ _ _ _ hl).
  exact: approximate_partial_quotient_section_graph ha.
- apply: (@approximate_limit_graph_equivalent R [the metricType R of E]
    [the topologicalType of real_line_metric R] _ _ _ _ _ _ _ hl)=> t y.
  exact: (iff_sym (@approximate_partial_quotient_section_graph a ha t y)).
Qed.
End ScalarPartial.
