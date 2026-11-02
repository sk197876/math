(** Federer (1969), 3.1.8, p. 217: measurable
    uniform small-growth-exception sets B_j and their exhaustion
    of the original domain. The coefficient is the proved
    lower-volume bound for overlapping balls. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanMetricSeparability EuclideanLebesgueBoxes
  EuclideanJointTranslationMeasurability EuclideanOverlapGoodPoint
  EuclideanSmallMassCutoffs EuclideanApproximateTranslation EuclideanApproximateContext
  RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasurableFunctionUP MeasurableTotalBasic ScalarRemainderMeasurability
  ApproximateMetricGrowth MeasureUP MeasureBasic MeasureFiniteClosure MeasureAlmostUP
  MeasureAlmostBasic BorelRegularMeasureUP ProductMeasure ProductSections
  MetricClosedBalls CenteredBallRelations MeasureSetDensity ExtendedRealReciprocalBounds RealLatticeTruncationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section GrowthCutoffs.
Variable R : realType.
Variable m : nat.
Variable Y : metricType R.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation mu := (@euclidean_lebesgue_measure R m).
Variables A : set X.
Variable f : X->Y.

(** Source for [euclidean_growth_exception_section]: translated
    exceptional points in Q(u,r,j), Federer 3.1.8, p. 217.
    Its radius restriction is imposed by the cutoff below. *)
Definition euclidean_growth_exception_section (M : R) : set (X*X)%type :=
  [set ah | metric_growth_exception A f ah.1 M (ah.1+ah.2)].

(** Source for [euclidean_growth_cutoff]: the measurable
    uniform sets B_j in Federer 3.1.8, p. 217.
    Index j denotes positive integer j+1. Closed balls and a
    smaller positive volume coefficient give the same covering
    and Lipschitz conclusions. *)
Definition euclidean_growth_cutoff (j : nat) : set X :=
  A `&` euclidean_small_mass_cutoff
    (euclidean_growth_exception_section (j.+1%:R))
    (euclidean_overlap_mass_coefficient R m) j.

(** Source for [euclidean_growth_exception_section_measurable]:
    measurability needed for the application of 3.1.3 to B_j,
    Federer 3.1.8, p. 217. *)
Lemma euclidean_growth_exception_section_measurable (D : set Y) M :
  countable D -> dense D -> measure_measurable mu A ->
  is_measure_measurable_function mu (partial_function_total f) ->
  measure_measurable
    (product_measure (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R m))
    (euclidean_growth_exception_section M).
Proof.
move=> hc hd hA hf.
pose hmu := euclidean_lebesgue_is_measure R m.
pose nu := product_measure hmu hmu.
pose hnu := product_measure_is_measure hmu hmu.
have hy := euclidean_joint_translation_distance_measurable hc hd hf.
have [Dx [hDxc hDxd]] := euclidean_metric_separable R m.
have hi : is_measure_measurable_function mu (partial_function_total (fun x : X=>x)).
  constructor.
  - rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hmu.
  - move=> W hW; rewrite partial_function_total_preimage.
    change (measure_measurable mu W).
    exact (@borel_regular_open_measurable R [the topologicalType of X] mu
      (euclidean_lebesgue_borel_regular R m) W hW).
have hx := euclidean_joint_translation_distance_measurable hDxc hDxd hi.
have hleft := measurable_total_real_multiply hnu
  (measurable_total_constant hnu (M : real_line_metric R)) hx.
have hcomp := measurable_total_real_strict_comparison hnu hleft hy.
have hmissing := measure_measurable_complement
  (euclidean_joint_translation_set_measurable hA).
exact: (measure_measurable_union hnu hmissing hcomp).
Qed.

(** Source for [euclidean_growth_cutoff_measurable]:
    the assertion that each B_j is Lebesgue measurable,
    Federer 3.1.8, p. 217. *)
Lemma euclidean_growth_cutoff_measurable (D : set Y) j :
  countable D -> dense D -> measure_measurable mu A ->
  is_measure_measurable_function mu (partial_function_total f) ->
  measure_measurable mu (euclidean_growth_cutoff j).
Proof.
move=> hc hd hA hf; apply: (measure_measurable_intersection
  (euclidean_lebesgue_is_measure R m) hA _).
apply: euclidean_small_mass_cutoff_measurable.
exact: euclidean_growth_exception_section_measurable hc hd hA hf.
Qed.

(** Source for [euclidean_growth_exception_antitone]:
    increasing j shrinks the exceptional set Q(u,r,j),
    supporting the exhaustion in Federer 3.1.8, p. 217. *)
Lemma euclidean_growth_exception_antitone a M N :
  M<=N -> metric_growth_exception A f a N `<=` metric_growth_exception A f a M.
Proof.
move=> hMN x [hn|hb]; first by left.
right; apply: le_lt_trans _ hb.
apply: ler_wpM2r; [exact: mdist_ge0|exact hMN].
Qed.

(** Source for [euclidean_growth_cutoff_covers]:
    the equality A=union_j B_j in Federer 3.1.8,
    p. 217. A finite coefficient and a positive cutoff
    radius are dominated by one sufficiently large natural index. *)
Theorem euclidean_growth_cutoff_covers a :
  A a ->
  (exists M : R, 0<M /\ partial_function_graph
    (measure_set_density mu (@centered_closed_ball_relation R [the metricType R of X])
      (metric_growth_exception A f a M)) a 0%E) ->
  exists j, euclidean_growth_cutoff j a.
Proof.
move=> ha [M [hM hzero]].
have ht := @euclidean_zero_density_translation R m a (0 : X)
  (metric_growth_exception A f a M).
rewrite addr0 in ht.
have hsection := ht hzero.
have [p hp] := @euclidean_zero_density_has_small_mass_cutoff R m m
  (euclidean_growth_exception_section M) (euclidean_overlap_mass_coefficient R m) a
  (euclidean_overlap_mass_coefficient_positive R m) hsection.
pose N := Num.bound M.
pose j := maxn N p.
have hMj : M<j.+1%:R.
  apply: lt_le_trans (archi_boundP (ltW hM)) _.
  rewrite ler_nat; exact: leq_trans (leq_maxl N p) (leqnSn j).
exists j; split=> // r hr hrj.
have hrp : r<(p.+1%:R : R)^-1.
  exact: lt_le_trans hrj (@positive_reciprocal_nat_antitone R p j (leq_maxr N p)).
apply: le_trans _ (hp r hr hrp).
apply: (@measure_mono R [the choiceType of X] mu
  (euclidean_lebesgue_is_measure R m) _ _).
move=> h [hh hball].
split=> //.
exact: (@euclidean_growth_exception_antitone a M (j.+1%:R) (ltW hMj) (a+h) hh).
Qed.

(** Source for [euclidean_growth_cutoff_ball_mass]:
    the Q(a,r,j) mass estimate supplied by B_j,
    Federer 3.1.8, p. 217, restored from increment
    coordinates using exact Lebesgue translation invariance. *)
Lemma euclidean_growth_cutoff_ball_mass j a r :
  euclidean_growth_cutoff j a -> 0<r -> r<(j.+1%:R)^-1 ->
  (mu (metric_growth_exception A f a (j.+1%:R) `&` metric_closed_ball a r)<=
    (euclidean_overlap_mass_coefficient R m*r^+m)%:E)%E.
Proof.
move=> [_ hcut] hr hsmall; have h := hcut r hr hsmall.
change (is_true (mu (((fun h : X=>(a+h)%R) @^-1`
  metric_growth_exception A f a (j.+1%:R)) `&`
  metric_closed_ball (0%R : X) r)<=(euclidean_overlap_mass_coefficient R m*r^+m)%:E)%E) in h.
by rewrite euclidean_translated_section_ball_mass addr0 in h.
Qed.
End GrowthCutoffs.
