(** Federer (1969), 3.2.35, p. 272:
    actual strict distance sublevels are the
    existing unions of open balls about S. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import MetricSetDistanceUP MetricSetDistanceClosure MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_distance_tube_thickening]:
    supporting exact original distance tubes in
    Federer 3.2.35, p. 272. Approximation
    in the abstract infimum gives an original
    centre within r; the reverse inclusion is
    the distance lower law. This equality
    uses no convexity, closedness or measurability. *)
Lemma metric_distance_tube_thickening (R:realType) (X:metricType R) (S:set X) d r:
  is_metric_set_distance S d ->[set x|d x<r]=metric_open_thickening S r.
Proof.
move=>hD; apply/seteqP; split=>x.
- move=>hx; have hError:0<r-d x by rewrite subr_gt0.
  have [a [ha hNear]]:=metric_set_distance_approximation hD x hError.
  have hSimplify:d x+(r-d x)=r by rewrite addrC subrK.
  rewrite hSimplify in hNear.
  exists a=>//; change (is_true (mdist a x<r)); by rewrite metric_sym.
- move=>[a ha hNear]; change (is_true (mdist a x<r)) in hNear.
  apply:(le_lt_trans (@metric_set_distance_lower R X S d hD x a ha) _).
  by rewrite metric_sym.
Qed.
