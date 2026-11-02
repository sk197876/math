(** Federer (1969), 2.10.46, pp. 203–204: collect the Caratheodory and Gross
    upper inequalities for arbitrary factors in all natural dimensions,
    retaining the ordinary defined-product domain of 2.1.1, p. 51. Null
    second factors and zero-dimensional first factors use the independently
    proved endpoint extensions. The lower Gross inequality is not inferred
    from these upper bounds. Source context and covering proof:
    ConvexBallProductCutoff.v and GrossBallProductCutoff.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates MetricProductRectangles
  EuclideanLebesgueDimensions ProjectionMeasure ProjectionProductEmptyBlock
  GrossProductUpperBound ConvexProductUpperBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [caratheodory_projection_product_upper_bound]:
    upper product inequality of 2.10.46, p. 203,
    for arbitrary sets on the ordinary product domain. The
    zero-dimensional first-factor case is an explicit auxiliary
    extension using the existing unit-mass convention. *)
Theorem caratheodory_projection_product_upper_bound (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N ->
  ((@caratheodory_projection_measure R n k V< +oo)%E \/
    (0<euclidean_lebesgue_measure m U)%E) ->
  (@caratheodory_projection_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)<=
    euclidean_lebesgue_measure m U*@caratheodory_projection_measure R n k V)%E.
Proof.
case: m U=> [|m] U hkn hdom.
- by rewrite (@convex_product_empty_first_block R n k U V hkn).
- exact: caratheodory_projection_product_upper_defined.
Qed.

(** Source for [gross_product_upper_bound]: the same upper
    product inequality for Gross measure in 2.10.46,
    p. 204, on arbitrary sets. The general lower
    inequality is a separate mathematical obligation. *)
Theorem gross_product_upper_bound (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (k<=n)%N ->
  ((@gross_measure R n k V< +oo)%E \/
    (0<euclidean_lebesgue_measure m U)%E) ->
  (@gross_measure R (m+n) (m+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m n z).1)
    (fun z=>(@euclidean_block_split R m n z).2) U V)<=
    euclidean_lebesgue_measure m U*@gross_measure R n k V)%E.
Proof.
case: m U=> [|m] U hkn hdom.
- by rewrite (@gross_product_empty_first_block R n k U V hkn).
- exact: gross_product_upper_defined.
Qed.
