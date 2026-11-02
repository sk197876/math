(** Federer (1969), 2.10.13, p. 177, second assertion and final proof
    paragraph: absolute continuity is equivalent to finite variation
    together with preservation of Lebesgue-null sets as H1-null images. The
    proof uses only the scalar arc-length parameter, its induced measure,
    and 2.9.20, pp. 165–166. Consequently the finite-family metric notion
    admits the criterion in every metric target; reflexivity is unnecessary
    for this part, unlike the derivative-integral assertions of 2.9.22, pp.
    167–168. This strengthening is recorded explicitly. No relevant
    correction occurs in the local Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import IntervalBumpFunctions RealMetricBackground RealLineSeparability CurveVariationUP CurveArcLength
  MetricCurveLocalization MetricAbsoluteContinuityFiniteVariation MetricCurveAbsoluteContinuityUP
  MetricAbsoluteContinuityArcLength ArcLengthImageMeasure StieltjesContinuityPoints StieltjesMonotone
  StieltjesCaratheodory StieltjesCaratheodoryConsequences StieltjesCaratheodoryIdentification
  RealAbsoluteContinuityUP RealAbsoluteContinuity MeasureUP MeasureBasic MeasureAlmostBasic
  MeasureRestriction MeasureAbsoluteContinuity ImageNullAbsoluteContinuity BorelImageCoverCost
  BorelCaratheodoryMeasure BorelRegularMeasureUP TopologicalBorel LebesgueScalarMeasure
  HausdorffLength HausdorffLengthCompatibility HausdorffMeasure StieltjesSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_maps_null_sets_to_null_length]: direct null-set
    condition in the second assertion of 2.10.13, p. 177.
    Quantify over all subsets T of [a,b], not merely measurable
    or Borel subsets. This definition uses the existing H1 interface. *)
Definition curve_maps_null_sets_to_null_length (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) := forall T : set (real_line_metric R),
  T `<=` `[a,b] -> lebesgue_scalar_measure T=0 -> @hausdorff_length R Y (g @` T)=0.

(** Source for [null_endpoints_restricted_interval_agreement]: supporting
    equivalence of the open restrictions in 2.9.20(4), p. 165,
    and the closed restriction in the proof of 2.10.13, p. 177.
    Restricting first to an arbitrary test set preserves null endpoints. *)
Lemma null_endpoints_restricted_interval_agreement (R : realType)
    (mu : set R -> \bar R) (a b : R) : is_measure mu ->
  mu [set a]=0 -> mu [set b]=0 ->
  measure_restrict mu `[a,b]=measure_restrict mu `]a,b[.
Proof.
move=> hm ha hb; apply/funext=> N.
have hzero x : mu [set x]=0 -> measure_restrict mu N [set x]=0.
  move=> hx; rewrite /measure_restrict.
  have hsub : N `&` [set x] `<=` [set x] by move=> z [].
  have hh := measure_mono hm hsub; rewrite hx in hh.
  by apply/eqP; rewrite eq_le hh (measure_nonnegative hm _).
have he := @measure_segment_open_interval R (measure_restrict mu N) a b
  (measure_restrict_is_measure hm N) (hzero a ha) (hzero b hb).
by rewrite /measure_restrict !(setIC N) in he.
Qed.

(** Source for [continuous_bv_curve_null_image_criterion]: supporting
    bounded-variation version of the second assertion of 2.10.13,
    p. 177. Identify the image measure with the actual measure
    induced by s, then apply 2.9.20 to s. This uses the
    arc-length finite-family equivalence, not a vector derivative
    theorem, so no completeness or reflexivity hypothesis is needed. *)
Theorem continuous_bv_curve_null_image_criterion (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : curve_locally_finite_variation g ->
  continuous (g : real_line_metric R -> Y) -> (a<b)%R ->
  (is_absolutely_continuous_metric_curve g a b <-> curve_maps_null_sets_to_null_length g a b).
Proof.
move=> hg hc hab.
pose s := arc_length g.
pose mu := stieltjes_caratheodory_measure s.
have hs := @arc_length_monotone R Y g hg.
have hsf := monotone_locally_finite_variation hs.
have hsc := continuous_curve_arc_length_continuous hg hc.
have hp := stieltjes_caratheodory_induced_pair hs.
have hm := stieltjes_caratheodory_is_measure hs.
have hpoint x : mu [set x]=0.
  exact: stieltjes_caratheodory_continuity_point_null hs (hsc x).
have hrestr := @null_endpoints_restricted_interval_agreement R mu a b hm (hpoint a) (hpoint b).
have [D [hD hden]] := real_line_countable_dense R.
have hImage := @image_null_absolute_continuity R [the metricType R of real_line_metric R] Y g
  (@hausdorff_length R Y) (@lebesgue_scalar_measure R) D `[a,b]
  (@hausdorff_length_is_measure R Y) (lebesgue_scalar_is_measure R)
  (lebesgue_scalar_borel_regular R) hD hden (closed_borel_set (@segment_closed_real R a b)).
rewrite /mu /s in hrestr.
rewrite (@continuous_curve_arc_length_image_measure R Y g hg hc) hrestr in hImage.
have hscalar := (@federer_2_9_20 R s mu (fun _ => 0) a b hsf hp hab).2.2.
have harc := @metric_absolute_continuity_arc_length R Y g a b hg.
split.
- move=> hAC; apply: hImage.1.
  exact: (hscalar.1 (harc.1 hAC)).2.1.
- move=> hNull; apply: harc.2; apply: hscalar.2.
  have hcs : continuous (s : real_line_metric R -> real_line_metric R) := hsc.
  split; first exact: continuous_subspaceT hcs.
  split; first exact: hImage.2 hNull.
  by move=> N hN; rewrite /measure_restrict.
Qed.

(** Source for [curve_null_image_condition_equal_on]: supporting
    interval locality of the null-image condition in 2.10.13,
    p. 177. A representative agreeing on [a,b] has exactly
    the same image of each of its arbitrary subsets. *)
Lemma curve_null_image_condition_equal_on (R : realType) (Y : metricType R)
    (g h : R -> Y) (a b : R) :
  (forall x, (a<=x<=b)%R -> g x=h x) ->
  (curve_maps_null_sets_to_null_length g a b <-> curve_maps_null_sets_to_null_length h a b).
Proof.
move=> he.
have hImage T : T `<=` `[a,b] -> g @` T=h @` T.
  move=> hT; apply/seteqP; split=> y [x hx <-]; exists x=> //.
  - apply: esym; apply: he; by have := hT x hx; rewrite /= in_itv /=.
  - apply: he; by have := hT x hx; rewrite /= in_itv /=.
split=> hNull T hT hzero.
- by rewrite -(hImage T hT); exact: hNull T hT hzero.
- by rewrite (hImage T hT); exact: hNull T hT hzero.
Qed.

(** Source for [continuous_curve_null_image_criterion]: direct
    second assertion of 2.10.13, p. 177, strengthened to every
    metric target for the finite-family notion of absolute continuity.
    Absolute continuity supplies finite variation; the converse uses
    only finite variation on [a,b]. A retracted proof representative
    removes any bounded-variation condition outside that interval. *)
Theorem continuous_curve_null_image_criterion (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) : continuous (g : real_line_metric R -> Y) -> (a<b)%R ->
  (is_absolutely_continuous_metric_curve g a b <->
    curve_variation g a b < +oo /\ curve_maps_null_sets_to_null_length g a b).
Proof.
move=> hg hab.
pose h := g \o @segment_retraction R a b.
have he x : (a<=x<=b)%R -> h x=g x.
  by move=> hx; rewrite /h /= segment_retraction_id.
have hAC := @metric_absolute_continuity_equal_on R Y h g a b he.
have hNull := @curve_null_image_condition_equal_on R Y h g a b he.
have hc : continuous (h : real_line_metric R -> Y) := @metric_retracted_curve_continuous R Y g a b hg.
split.
- move=> hAg.
  have hfin := metric_absolute_continuity_finite_variation (ltW hab) hAg.
  split=> //; apply: hNull.1.
  apply: (@continuous_bv_curve_null_image_criterion R Y h a b
    (metric_finite_interval_retracted_variation (ltW hab) hfin) hc hab).1.
  exact: hAC.2 hAg.
- move=> [hfin hNg]; apply: hAC.1.
  apply: (@continuous_bv_curve_null_image_criterion R Y h a b
    (metric_finite_interval_retracted_variation (ltW hab) hfin) hc hab).2.
  exact: hNull.2 hNg.
Qed.
