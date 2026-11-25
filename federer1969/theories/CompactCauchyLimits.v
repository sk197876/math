(** General metric topology supporting the Suslin-image
    argument in Federer (1969), 2.10.5, p. 172.
    A proper Cauchy filter with a cluster point
    converges; a compact set belonging to the filter
    supplies such a point. These are background facts
    for the complete parameter space used with 2.2.10,
    p. 65, not extra measure assertions. Source
    editions and completeness conventions: CompleteMetricUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From mathcomp Require Import lra.
From Federer Require Import CompleteMetricUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_cauchy_cluster_converges]: supporting
    Cauchy-filter fact for the complete metric spaces
    in the Suslin argument of Federer 2.10.5, p. 172.
    A small Cauchy ball and a nearby cluster point
    control every member of that ball. *)
Lemma metric_cauchy_cluster_converges (R : realType) (X : metricType R)
    (F : set_system X) (PF : ProperFilter F) (x : X) :
  cauchy F -> cluster F x -> F --> x.
Proof.
move=> hC hx W hW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP x W) hW.
have hepos : 0<e := he.
pose d := e/4.
have hd : 0<d by rewrite /d divr_gt0.
have [a hA] := proj1 (@cauchyP R X F PF) hC d hd.
have [z [hza hxz]] := hx (ball a d) (ball x d) hA (nbhsx_ballx x d hd).
rewrite !ballEmdist in hza hxz.
have haz : mdist a z<d := hza.
have hxz' : mdist x z<d := hxz.
have FF : Filter F := @filter_filter _ F PF.
apply: (@filterS _ F FF _ _ _ hA)=> y hy; apply: hball.
rewrite ballEmdist in hy.
have hay : mdist a y<d := hy.
have htri := metric_triangle x z y.
have htri' := metric_triangle z a y; rewrite (metric_sym z a) in htri'.
rewrite /d in haz hxz' hay; change (is_true (mdist x y<e)); lra.
Qed.

(** Source for [compact_cauchy_filter_limit]: supporting
    compactness-to-completeness step for the projection
    parameter space of Federer 2.10.5, p. 172.
    The compact set may be empty; properness then
    prevents it from belonging to the filter. *)
Theorem compact_cauchy_filter_limit (R : realType) (X : metricType R)
    (K : set X) (F : set_system X) (PF : ProperFilter F) :
  compact K -> F K -> cauchy F -> exists x, K x /\ F --> x.
Proof.
move=> hK hFK hC; have [x [hx hcluster]] := hK F PF hFK.
exists x; split=> //; exact (@metric_cauchy_cluster_converges R X F PF x hC hcluster).
Qed.

(** Source for [compact_metric_space_complete]: supporting
    completeness of compact metric parameter spaces
    for Federer 2.10.5, p. 172, before applying
    the continuous Suslin-image theorem of 2.2.10. *)
Theorem compact_metric_space_complete (R : realType) (X : metricType R) :
  compact (@setT X) -> is_complete_metric_space X.
Proof.
move=> hX F PF hC.
have [x [_ hx]] := @compact_cauchy_filter_limit R X setT F PF hX (@filterT _ F (@filter_filter _ F PF)) hC.
by exists x.
Qed.
