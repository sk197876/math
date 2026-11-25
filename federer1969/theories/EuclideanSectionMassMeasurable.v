(** Federer (1969), 3.1.3(1), pp. 212–213: measurable small-section
    mass bounds. Fubini gives measurability at each fixed radius; a
    countable intersection over rational radii gives the asserted set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology normedtype realfun.
From Federer Require Import RealMetricBackground GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume MetricClosedBalls MeasureUP MeasureBasic MeasureSplit CountablyMeasurableUP PartialFunctionUP MeasureFiniteClosure
  MeasureCountableClosure BorelRegularMeasureUP TopologicalBorel ProductMeasure
  ProductRectangleValue ProductSections ProductSetFubini CountablyMeasurableSubsets
  CountablyMeasurableProduct PartialFunctionBasic MeasurableFunctionUP
  MeasurableFunctionBorel CountableOrderIntervals ExtendedRealOrderTopology
  RationalRadiusBounds RealDilationSlack.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Import numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_section_ball_mass_measurable]: the Fubini
    assertion about S_r in Federer 3.1.3(1), p. 213. Actual outer
    measures of all sections are retained, including exceptional sections;
    completeness of the measure handles those exceptional parameter values. *)
Lemma euclidean_section_ball_mass_measurable (R : realType) m k
    (S : set (inner_metric_space (@euclidean_inner_productP R m) *
      inner_metric_space (@euclidean_inner_productP R k))) r :
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R k)) S ->
  @is_measure_measurable_function R _ [the topologicalType of extended_real_line R]
    (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun x => euclidean_lebesgue_measure k
      (product_vertical_section S x `&` metric_closed_ball ((0%R : R_n R k) : inner_metric_space (@euclidean_inner_productP R k)) r))).
Proof.
move=> hS.
pose alpha := @euclidean_lebesgue_measure R m.
pose beta := @euclidean_lebesgue_measure R k.
pose ha := euclidean_lebesgue_is_measure R m.
pose hb := euclidean_lebesgue_is_measure R k.
pose B := @metric_closed_ball R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R k)] 0%R r.
have hB : measure_measurable beta B.
  apply: (borel_regular_borel_measurable hb (euclidean_lebesgue_borel_regular R k)).
  apply: closed_borel_set; exact: metric_closed_ball_closed.
pose Sr := S `&` (setT `*` B).
have hSr : measure_measurable (product_measure ha hb) Sr.
  apply: (@measure_measurable_intersection R _ _ (product_measure_is_measure ha hb) S (setT `*` B) hS).
  exact: (product_measure_measurable_rectangle ha hb (measure_measurable_whole ha) hB).1.
have hc : measure_countably_measurable (product_measure ha hb) Sr.
  apply: (measurable_subset_countably_measurable (product_measure_is_measure ha hb) hSr (fun x _=>Logic.I)).
  exact: product_whole_countably_measurable
    (euclidean_lebesgue_countably_measurable R m) (euclidean_lebesgue_countably_measurable R k).
have hi := (product_set_fubini hc).2.2.1.1.
have he x : product_vertical_section Sr x=product_vertical_section S x `&` B.
  apply/seteqP; split; first by move=> z [hz [_ hbz]]; split.
  by move=> z [hz hbz]; split=> //; split.
have hf : (fun x => beta (product_vertical_section Sr x))=
    (fun x => beta (product_vertical_section S x `&` B)).
  by apply: funext=> x; rewrite he.
by rewrite hf in hi.
Qed.

(** Source for [euclidean_small_section_mass_measurable]: the whole
    assertion (1) in Federer 3.1.3, pp. 212–213. The ball-mass bound
    for every 0<r<d is equivalent to its rational-radius restriction.
    The proof also permits arbitrary real coefficients and cutoffs. *)
Theorem euclidean_small_section_mass_measurable (R : realType) m k
    (S : set (inner_metric_space (@euclidean_inner_productP R m) *
      inner_metric_space (@euclidean_inner_productP R k))) (c d : R) :
  measure_measurable (product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R k)) S ->
  measure_measurable (@euclidean_lebesgue_measure R m)
    [set x | forall r : R, (0<r)%R -> (r<d)%R ->
      euclidean_lebesgue_measure k (product_vertical_section S x `&` metric_closed_ball ((0%R : R_n R k) : inner_metric_space (@euclidean_inner_productP R k)) r)
        <= (c*euclidean_unit_ball_volume R k*r^+k)%R%:E].
Proof.
move=> hS.
pose F x r := euclidean_lebesgue_measure k
  (product_vertical_section S x `&` metric_closed_ball ((0%R : R_n R k) : inner_metric_space (@euclidean_inner_productP R k)) r).
pose g (r : real_line_metric R) : real_line_metric R := (c*euclidean_unit_ball_volume R k*r^+k)%R.
have hg : continuous g.
  rewrite /g; move=> r; apply: (@continuousM R R^o
    (fun _=>(c*euclidean_unit_ball_volume R k)%R) (fun z=>(z^+k)%R) r).
  - exact: cst_continuous.
  - exact: real_integral_power_continuous.
have he : [set x | forall r : R, (0<r)%R -> (r<d)%R -> F x r<=(g r)%:E]=
    \bigcap_(q in [set q : rat | (0<(ratr q : R))%R /\ (ratr q<d)%R])
      [set x | F x (ratr q)<=(g (ratr q))%:E].
  apply/seteqP; split=> x hx.
  - by move=> q [hq0 hqd]; exact: hx _ hq0 hqd.
  - apply: (monotone_rational_radius_bound _ hg)=> [r s hr hrs|q hq0 hqd].
    + apply: (measure_mono (euclidean_lebesgue_is_measure R k))=> z [hz hb].
      split=> //; exact: le_trans hb hrs.
    + exact: hx q (conj hq0 hqd).
change (measure_measurable (@euclidean_lebesgue_measure R m)
  [set x | forall r : R, (0<r)%R -> (r<d)%R -> F x r<=(g r)%:E]).
rewrite he; apply: (measure_measurable_countable_intersection (euclidean_lebesgue_is_measure R m)).
- exact: countableP.
- move=> q _.
  have hf := euclidean_section_ball_mass_measurable (ratr q) hS.
  have hpre := @measurable_function_borel_preimage R _
    [the topologicalType of extended_real_line R] (@euclidean_lebesgue_measure R m)
    (euclidean_lebesgue_is_measure R m) _ hf
    [set y | y<=(g (ratr q))%:E]
    (closed_borel_set (@order_closed_lower_ray_closed _ [the orderTopologicalType _ of order_topology (\bar R)] (g (ratr q))%:E)).
  have hset : partial_function_preimage (partial_function_total (F^~ (ratr q)))
      [set y | y<=(g (ratr q))%:E]=[set x | F x (ratr q)<=(g (ratr q))%:E].
    apply/seteqP; split; first by move=> x [y [<- hy]].
    by move=> x hx; exists (F x (ratr q)); split.
  by rewrite hset in hpre.
Qed.
