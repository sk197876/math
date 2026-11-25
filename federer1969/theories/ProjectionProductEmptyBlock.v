(** Federer (1969), 2.10.46, pp. 203–204: explicit zero-dimensional
    first-factor extension of the product assertions. The book's
    positive-dimensional projection measures are extended using the existing
    unit mass on R^0 from EuclideanLebesgueDimensions.v. This convention is
    auxiliary and is not attributed to the printed theorem. No measurability
    of either factor is needed here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import FiniteCoordinates EuclideanInnerProduct InnerMetric EuclideanCoordinateLists
  EuclideanBlockCoordinates EuclideanBlockMeasure MetricProductRectangles EuclideanLebesgueDimensions
  ProjectionMeasure MeasureUP MeasureBasic PointMassMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_measure_dimension_transport]: supporting
    equality-of-dimension transport for the empty first block
    in the auxiliary extension of 2.10.46, p. 204.
    It changes only the representation of equal natural numbers. *)
Lemma gross_measure_dimension_transport (R : realType) a b d e
    (ha : a=b) (hd : d=e) (A : set (inner_metric_space (@euclidean_inner_productP R b))) :
  @gross_measure R a d ((@euclidean_dimension_cast R a b ha) @^-1` A)=@gross_measure R b e A.
Proof.
case: b / ha A=> A; case: e / hd.
by rewrite /euclidean_dimension_cast preimage_id.
Qed.

(** Source for [convex_projection_measure_dimension_transport]:
    supporting equal-dimension transport for the auxiliary empty
    first block in 2.10.46, p. 203. *)
Lemma convex_projection_measure_dimension_transport (R : realType) a b d e
    (ha : a=b) (hd : d=e) (A : set (inner_metric_space (@euclidean_inner_productP R b))) :
  @caratheodory_projection_measure R a d ((@euclidean_dimension_cast R a b ha) @^-1` A)=
    @caratheodory_projection_measure R b e A.
Proof.
case: b / ha A=> A; case: e / hd.
by rewrite /euclidean_dimension_cast preimage_id.
Qed.

(** Source for [euclidean_empty_block_rectangle]: supporting
    set identity for the zero-dimensional extension of 2.10.46,
    pp. 203–204. An inhabited R^0 factor contributes
    exactly the transported second set. *)
Lemma euclidean_empty_block_rectangle (R : realType) n
    (U : set (inner_metric_space (@euclidean_inner_productP R 0)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) : U 0 ->
  metric_product_rectangle (fun z=>(@euclidean_block_split R 0 n z).1)
    (fun z=>(@euclidean_block_split R 0 n z).2) U V=
    (@euclidean_dimension_cast R (0+n) n (add0n n)) @^-1` V.
Proof.
move=> hU; apply/seteqP; split=> x.
- change (U ((@euclidean_block_split R 0 n x).1) /\ V ((@euclidean_block_split R 0 n x).2) -> V (euclidean_dimension_cast (add0n n) x)).
  by rewrite euclidean_block_left_empty; move=> [_ hx].
- move=> hx; change (U ((@euclidean_block_split R 0 n x).1) /\ V ((@euclidean_block_split R 0 n x).2)).
  by rewrite euclidean_block_left_empty.
Qed.

(** Source for [gross_product_empty_first_block]: auxiliary
    zero-dimensional extension of the Gross product equality
    in 2.10.46, p. 204. Empty first sets give
    a directly proved null product, even for infinite second mass. *)
Theorem gross_product_empty_first_block (R : realType) n k
    (U : set (inner_metric_space (@euclidean_inner_productP R 0)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) : (k<=n)%N ->
  @gross_measure R (0+n) (0+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R 0 n z).1)
    (fun z=>(@euclidean_block_split R 0 n z).2) U V)=
    (euclidean_lebesgue_measure 0 U*@gross_measure R n k V)%E.
Proof.
move=> hkn; case: (pselect (U 0))=> hU.
- rewrite (@euclidean_empty_block_rectangle R n U V hU)
    (@gross_measure_dimension_transport R (0+n) n (0+k) k (add0n n) (add0n k) V).
  change (@gross_measure R n k V=(@point_mass R (inner_metric_space (@euclidean_inner_productP R 0)) 0%R U*@gross_measure R n k V)%E).
  by rewrite (point_mass_in R hU) mul1e.
- have hU0 : U=set0.
    apply/seteqP; split=> // x hx; exfalso; apply: hU; by rewrite -(@coordinate_zero R x).
  rewrite hU0 metric_product_rectangle_empty_left (measure_empty (euclidean_lebesgue_is_measure R 0)) mul0e.
  apply: measure_empty; apply: gross_measure_is_measure; by rewrite !add0n.
Qed.

(** Source for [convex_product_empty_first_block]: auxiliary
    zero-dimensional first-factor extension of the Caratheodory
    product inequality in 2.10.46, p. 203.
    In this dimension the two sides are equal. *)
Theorem convex_product_empty_first_block (R : realType) n k
    (U : set (inner_metric_space (@euclidean_inner_productP R 0)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) : (k<=n)%N ->
  @caratheodory_projection_measure R (0+n) (0+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R 0 n z).1)
    (fun z=>(@euclidean_block_split R 0 n z).2) U V)=
    (euclidean_lebesgue_measure 0 U*@caratheodory_projection_measure R n k V)%E.
Proof.
move=> hkn; case: (pselect (U 0))=> hU.
- rewrite (@euclidean_empty_block_rectangle R n U V hU)
    (@convex_projection_measure_dimension_transport R (0+n) n (0+k) k (add0n n) (add0n k) V).
  change (@caratheodory_projection_measure R n k V=
    (@point_mass R (inner_metric_space (@euclidean_inner_productP R 0)) 0%R U*@caratheodory_projection_measure R n k V)%E).
  by rewrite (point_mass_in R hU) mul1e.
- have hU0 : U=set0.
    apply/seteqP; split=> // x hx; exfalso; apply: hU; by rewrite -(@coordinate_zero R x).
  rewrite hU0 metric_product_rectangle_empty_left (measure_empty (euclidean_lebesgue_is_measure R 0)) mul0e.
  apply: measure_empty; apply: caratheodory_projection_measure_is_measure; by rewrite !add0n.
Qed.
