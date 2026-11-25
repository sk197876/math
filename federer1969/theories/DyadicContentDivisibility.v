(** Federer (1969), 2.10.47(3), p. 205: every real value between zero and
    gamma_i(E) is attained on a compact subset of compact E. Here the
    abstract slice lemmas are instantiated with the actual dyadic covering
    content. All neighbourhood and finiteness conditions follow from the
    proved cutoff comparisons. Source context: CompactContentDivisibility.v
    and DyadicContentNullNeighborhood.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanCoordinateTopology DyadicCubeGridUP DyadicCubeGrid RefiningCoverContent
  DyadicContentFinite DyadicContentNullNeighborhood CompactContentDivisibility
  MetricDiameter MetricRealPowerCost MetricRealPowerMeasureUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dyadic_content_intermediate_compact_subset]:
    step (3) of 2.10.47, p. 205, under
    the null-coordinate-section reduction in the proof.
    Nullity is needed only for the selected coordinate's
    parallel levels. The real degree and coefficient
    are positive; the source may be empty. *)
Theorem dyadic_content_intermediate_compact_subset (R : realType) n (a : R_n R n) Q c p i gamma
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (E : set (inner_metric_space (@euclidean_inner_productP R n))) (l : 'I_n) (y : R) :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) i gamma ->
  is_metric_real_power_measure c p mu -> 0<c -> 0<p -> compact E ->
  (forall x, E x -> forall k, a k<=x k<=a k+1) ->
  (forall t : R, mu (E `&` [set x | x l=t])=0%E) ->
  0<=y -> (y%:E<=gamma E)%E ->
  exists D, [/\ compact D, D `<=` E & gamma D=y%:E].
Proof.
move=> hQ hg hmu hc hp hE hroot hlevels hy hyE.
pose X := inner_metric_space (@euclidean_inner_productP R n).
have hn : (0<n)%N := leq_ltn_trans (leq0n l) (ltn_ord l).
have hm := refining_cover_content_measure hg
  (fun S _=>@metric_real_power_cost_nonnegative R c p (extended_metric_diameter S) (ltW hc)).
apply: (@compact_content_intermediate_subset R X gamma hm E
  (fun x=>(x l : real_line_metric R)) y hE (@euclidean_coordinate_continuous R n l) _ _ hy hyE).
- exact: (@dyadic_power_content_root_finite R n a Q c p i gamma hQ hg (ltW hc) (ltW hp) E hroot).
- move=> t e he; exact: (@dyadic_content_null_set_neighbourhood R n a Q c p i gamma mu E
    (E `&` [set x | x l=t]) e hQ hg hmu hn hc hp he hroot (hlevels t)).
Qed.
