(** Federer (1969), 3.2.26(2), pp. 261–262:
    the convex integral-geometric upper comparison on every
    finite rectifiable set. Sum the disjoint compact charts;
    a genuine rectifiable Borel measure hull handles an
    arbitrary, possibly nonmeasurable, original source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableCompactChartsUP RectifiableCompactCharts RectifiableCompactChartLaws
  RectifiableCompactChartConvexMeasure RectifiableBorelMeasureHull
  IntegralGeometricMeasure GeometricHausdorffNullComparison HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureSplit MeasureIndexedCover MeasureCountableAdditivity
  MeasureHull BorelRegularMeasureUP TopologicalBorel NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_rectifiable_convex_geometric_upper]: the
    reduction by 3.2.18 in 3.2.26(2), p. 261,
    and its final cutoff limit on p. 262.
    Countable disjoint compact images carry all but a
    Hausdorff-null remainder. Their costs are bounded by
    their actual Hausdorff masses, with no overlap loss. *)
Theorem measurable_rectifiable_convex_geometric_upper (R:realType) m n
    (hmn:(m<=n)%N) (W:set (R_n R n)) (t: \bar R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->1<=t ->
  @convex_integral_geometric_measure R n m hmn t W<=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W.
Proof.
move=>hRect hW ht.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose Q:=@convex_integral_geometric_measure R n m hmn t.
have hH:=@hausdorff_measure_is_measure R X m.
have hQ:=@convex_integral_geometric_measure_is_measure R n m hmn t ht.
have hTwo:(1<(2:R))%R by rewrite ltr1n.
have hTwoPositive:(0<(2:R))%R by rewrite ltr0n.
have [K [psi hCover]]:=@federer_3_2_18 R m n 2%R W hRect hW hTwo.
pose F i:=psi i @` K i.
pose U:=\bigcup_i F i.
have hNull:Q (W `\` U)=0.
  exact:(@convex_integral_geometric_hausdorff_null R n m hmn t (W `\` U) ht hCover.2.2).
have hSplit:Q W<=Q (W `&` U)+Q (W `\` U):=measure_split_upper hQ W U.
rewrite hNull adde0 in hSplit.
have hCoverage:W `&` U `<=` \bigcup_i F i by move=>x [_ hx].
have hBound:=@measure_indexed_cover R (Choice.clone X _) [the choiceType of (nat:Type)]
  Q hQ (W `&` U) setT F (countableP setT) hCoverage.
have hComparison:nonnegative_sum setT (fun i=>Q (F i))<=
    nonnegative_sum setT (fun i=>H (F i)).
  apply:nonnegative_sum_mono=>i _.
  exact:(@compact_chart_convex_integral_geometric_upper R m n hmn 2%R (K i) (psi i) t
    hTwoPositive (hCover.1 i).1 ht).
have hMeas i:measure_measurable H (F i).
  apply:(borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m)).
  exact:(closed_borel_set (compact_closed (@metric_hausdorff R X)
    (uniform_compact_chart_image_compact (hCover.1 i).1))).
have hApart i j:i!=j ->forall x,F i x ->F j x ->False.
  move=>hij; exact:hCover.2.1 i j hij.
have hSum:nonnegative_sum setT (fun i=>H (F i))<=H W.
  rewrite -(@measure_sequence_disjoint_additivity R (Choice.clone X _) H hH F hMeas hApart).
  apply:(measure_mono hH)=>x [i _ hx]; exact:(hCover.1 i).2 x hx.
exact:(le_trans hSplit (le_trans hBound (le_trans hComparison hSum))).
Qed.

(** Source for [rectifiable_convex_geometric_upper]: the full
    arbitrary-source comparison H^m(W)>=Q_t^m(W) in
    3.2.26(2), pp. 261–262. Apply the measurable
    comparison to a finite rectifiable Borel measure hull M.
    Monotonicity and H^m(M)=H^m(W) suffice; its
    difference from nonmeasurable W is never asserted null. *)
Theorem rectifiable_convex_geometric_upper (R:realType) m n
    (hmn:(m<=n)%N) (W:set (R_n R n)) (t: \bar R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->1<=t ->
  @convex_integral_geometric_measure R n m hmn t W<=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W.
Proof.
move=>hRect ht.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose Q:=@convex_integral_geometric_measure R n m hmn t.
have hH:=@hausdorff_measure_is_measure R X m.
have hQ:=@convex_integral_geometric_measure_is_measure R n m hmn t ht.
have [M [hMBorel [hHull hMRect]]]:=rectifiable_borel_measure_hull hRect.
have hMMeas:=borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m) hMBorel.
have hUpper:=@measurable_rectifiable_convex_geometric_upper R m n hmn M t hMRect hMMeas ht.
have hMass:=measure_hull_equal_measure hH hHull.
rewrite -hMass in hUpper.
exact:(le_trans (measure_mono hQ (measure_hull_subset hHull)) hUpper).
Qed.
