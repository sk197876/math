(** Federer (1969), 3.2.16, p. 253:
    a compact family outside the approximate tangent
    cone generates a positive-ray set of zero
    m-density. Follow the finite open cone cover
    printed in the first paragraph. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormClosureLaws CompactFiniteCover
  PartialFunctionUP MeasureUP MeasureRestriction MetricDensities MetricDensityNumericalBounds
  MetricDensityZero MetricDensityZeroUnions MeasureApproximateTangentUP
  MeasureApproximateTangentCriterion ApproximateDirectionConeGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_nontangent_direction_hull_zero_density]:
    the complete first paragraph of Federer 3.2.16,
    p. 253: for compact C outside Tan_m(phi,a),
    T={a+r v:r>0,v in C} has zero m-density.
    No nonzero-direction or finite-ball-mass premise
    is added. *)
Theorem compact_nontangent_direction_hull_zero_density (R : realType)
    (X : lmodType R) (NX : X -> R) (hNX : is_real_norm NX)
    (phi : set X -> \bar R) m (a : X) (C : set X) :
  is_measure phi -> @compact (real_norm_metric_space hNX) C ->
  (forall v, C v -> ~measure_approximate_tangent_cone hNX phi m a v) ->
  partial_function_graph (@metric_density R (real_norm_metric_space hNX) m
    (measure_restrict phi (positive_directional_hull a C))) a 0.
Proof.
move=> hm hC hOutside; pose M := real_norm_metric_space hNX.
have hex v : exists e : R, (0<e)%R /\
    (C v -> @upper_metric_density R M m
      (measure_restrict phi (approximate_direction_cone NX a v e)) a=0).
  case: (pselect (C v))=> [hv|hv].
  - apply: contrapT=> hnone.
    apply: (@hOutside v hv).
    apply: (@measure_approximate_tangent_directional_criterion R X NX hNX phi m a v hm).2=> e he.
    have hnu := measure_restrict_is_measure hm (approximate_direction_cone NX a v e).
    have hnonneg := (@metric_densities_nonnegative R M m _ a hnu).2.
    rewrite lt_neqAle hnonneg andbT; apply/negP=> /eqP hEq.
    apply: hnone; exists e; split=> // _; exact: esym hEq.
  - exists 1%R; split; first exact: ltr01.
    by move=> /hv.
have [eps hEps] := choice hex.
pose E (v : M) : set M := approximate_direction_cone NX a v (eps v).
pose U (v : M) : set M := [set w | E v ((a+w)%R)].
have hU v : open (U v).
  exact: (@continuousP M M (fun w : M => ((a+w)%R : M))).1
    (@real_norm_metric_translate_continuous R X NX hNX a) (E v)
    (@approximate_direction_cone_open R X NX hNX a v (eps v)).
have hcover : C `<=` \bigcup_(v in C) U v.
  move=> v hv; exists v=> //.
  exact: (@approximate_direction_cone_center_direction R X NX hNX a v (eps v) (hEps v).1).
have [F hFC hFCover] := @compact_open_finite_cover M M C U C hC
  (fun v _ => hU v) hcover.
have hZero v : v \in F ->
    partial_function_graph (@metric_density R M m (measure_restrict phi (E v))) a 0.
  move=> hv; have hvC : C v := set_mem (hFC v hv).
  have hnu := measure_restrict_is_measure hm (E v).
  exact: (@metric_density_zero_iff_upper_zero R M m _ a hnu).2 ((hEps v).2 hvC).
have hUnion := @metric_restricted_density_zero_finite_union R M M m phi F E a hm hZero.
apply: (@metric_restricted_density_zero_subset R M m phi
  (positive_directional_hull a C) (\bigcup_(v in [set v | v \in F]) E v) a hm _ hUnion).
move=> x [t [w [ht [hw ->]]]].
have [v hv hUvw] := hFCover w hw.
exists v=> //; exact: (@approximate_direction_cone_positive_ray R X NX a v w (eps v) t ht hUvw).
Qed.
