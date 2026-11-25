(** Federer (1969), 3.3.19, p. 303: actual
    unit-speed affine lines used to choose original
    boundary points for the radial retraction argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric RealMetricBackground
  NormedAffineCurve NormMetricScaleContinuity LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_affine_line_distance]: exact actual
    unit-line isometry supporting the boundary choices in
    3.3.19, p. 303. No coordinate axis or
    supplied line chart is required. *)
Lemma unit_affine_line_distance (R:realType) n
    (z u:inner_metric_space (@euclidean_inner_productP R n)) (s t:R):
  inner_norm (@euclidean_inner_productP R n) u= 1 ->
  mdist (z+s*:u) (z+t*:u)=`|s-t|.
Proof. by move=>hu;rewrite inner_metric_distanceE affine_curve_increment inner_normZ hu mulr1. Qed.

(** Source for [unit_affine_line_continuous]: actual
    continuity of every original unit affine line,
    supporting the boundary-point choices in
    3.3.19, p. 303. *)
Lemma unit_affine_line_continuous (R:realType) n
    (z u:inner_metric_space (@euclidean_inner_productP R n)):
  inner_norm (@euclidean_inner_productP R n) u= 1 ->
  continuous (fun t:real_line_metric R=>(z+t*:u:inner_metric_space (@euclidean_inner_productP R n))).
Proof.
move=>hu;apply:(@metric_fixed_lipschitz_continuous R [the metricType R of real_line_metric R]
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
  (fun t=>z+t*:u) 1 ler01)=>s t.
by rewrite (@unit_affine_line_distance R n z u s t hu) real_line_metric_distanceE mul1r.
Qed.
