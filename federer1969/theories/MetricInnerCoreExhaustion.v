(** Federer (1969), 3.2.43, printed p. 278:
    the actual closed positive-distance inner cores exhaust
    the original interior as their radii decrease to zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import MetricOpenThickening ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_positive_core_interior]: supporting
    containment of the original inner cores in Int S,
    Federer 3.2.43, p. 278. The radius-r ball about each
    core point lies entirely in the original S. *)
Lemma metric_positive_core_interior (R:realType) (X:metricType R)
    (S:set X) (r:R):
  0<r ->(~`metric_open_thickening (~`S) r) `<=` interior S.
Proof.
move=>hr x hx; change (nbhs x S).
apply:(proj2 (metricType_numDomainType.nbhs_mdistP x S)).
exists r=>// y hNear; apply:contrapT=>hOutside; apply:hx.
exists y=>//; change (is_true (mdist y x<r)); by rewrite metric_sym.
Qed.

(** Source for [metric_inner_core_radius_antitone]: supporting
    monotonicity of the actual cores as r decreases in
    Federer 3.2.43, p. 278. No radius positivity is needed
    for this elementary set inclusion. *)
Lemma metric_inner_core_radius_antitone (R:realType) (X:metricType R)
    (S:set X) (s r:R):
  s<=r ->(~`metric_open_thickening (~`S) r) `<=`
    (~`metric_open_thickening (~`S) s).
Proof.
move=>hsr x hx [a ha hNear]; apply:hx.
exists a=>//; change (is_true (mdist a x<r)).
exact:lt_le_trans hNear hsr.
Qed.

(** Source for [metric_inner_core_reciprocal_exhaustion]: direct
    increasing-to-Int S observation in Federer 3.2.43,
    p. 278, represented by positive reciprocal natural
    radii. The neighbourhood criterion proves the exact
    union, including empty and whole original sources. *)
Theorem metric_inner_core_reciprocal_exhaustion (R:realType) (X:metricType R)
    (S:set X):
  (\bigcup_j (~`metric_open_thickening (~`S) (((j.+1)%:R:R)^-1)))=interior S.
Proof.
apply/seteqP; split=>x.
- move=>[j _ hx].
  have hRadius:0<((j.+1)%:R:R)^-1 by rewrite invr_gt0 ltr0n.
  exact:(@metric_positive_core_interior R X S _ hRadius x hx).
- move=>hInterior.
  have [d hd hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP x S) hInterior.
  have [j hSmall]:=positive_reciprocal_nat_small hd.
  exists j=>// hTube.
  have [a ha hNear]:=hTube.
  apply:ha; apply:hBall.
  change (is_true (mdist x a<d)); rewrite metric_sym; exact:lt_trans hNear hSmall.
Qed.
