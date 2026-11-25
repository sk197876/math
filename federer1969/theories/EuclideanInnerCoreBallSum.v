(** Federer (1969), 3.2.42, printed p. 278, second
    proof paragraph: adding the open radius-r ball to the
    actual inner core stays inside the original interior.
    The core is the complement of the actual open tube of
    the original complement. This also handles empty cores. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype lra.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology
  VectorSetSum MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_inner_core_ball_sum_interior]: direct
    containment Int(S) contains T+U(0,r) in the proof of
    Federer 3.2.42, p. 278. T is the actual radius-r core
    of the original S. No closedness, convexity, nonemptiness
    or measurability of S or T is imposed. *)
Lemma euclidean_inner_core_ball_sum_interior (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  vector_set_sum (~`metric_open_thickening (~`S) r) [set y | `|y|<r] `<=` interior S.
Proof.
move=>z /vector_set_sum_membership [a [b [hCore [hBall ->]]]].
change (nbhs (a+b) S).
apply:(proj2 (metricType_numDomainType.nbhs_mdistP (a+b) S)).
have hRadius:0<r-`|b| by rewrite subr_gt0.
exists (r-`|b|)=>// w hNear.
apply:contrapT=>hOutside; apply:hCore.
exists w=>//.
change (is_true (mdist w a<r)).
have hTriangle:=metric_triangle a (a+b) w.
have hIncrement:mdist a (a+b)=`|b| by rewrite inner_metric_normE addrC addKr.
rewrite hIncrement in hTriangle.
rewrite metric_sym.
have hLess:`|b|+mdist (a+b) w<r.
  change (is_true (mdist (a+b) w<r-`|b|)) in hNear.
  by move:hNear; rewrite ltrBrDr addrC.
exact:(le_lt_trans hTriangle hLess).
Qed.
