(** Federer (1969), 3.2.35, p. 271:
    translate an original convex body to contain
    zero while preserving its actual neighbourhoods. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_translation_distance]: supporting
    the translation reduction in Federer 3.2.35,
    p. 271, from the norm metric of
    1.7.1, p. 28. Addition of the
    same vector preserves every actual distance. *)
Lemma inner_translation_distance (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (a x y:V):
  mdist (x+a:inner_metric_space hB) (y+a)=mdist (x:inner_metric_space hB) y.
Proof. by rewrite !inner_metric_distanceE opprD addrA addrAC addrK. Qed.

(** Source for [inner_translation_neighbourhood]: supporting
    the original boundary under the translation
    reduction of Federer 3.2.35, p. 271.
    Equal distance balls give both exact
    neighbourhood implications. No compactness,
    convexity or boundary identity is assumed. *)
Lemma inner_translation_neighbourhood (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (a x:V) (U:set V):
  nbhs (x+a:inner_metric_space hB) U <->
  nbhs (x:inner_metric_space hB) ((fun z:V=>z+a) @^-1` U).
Proof.
split=>hU.
- have [r hr hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP
    (x+a:inner_metric_space hB) U) hU.
  apply:(proj2 (metricType_numDomainType.nbhs_mdistP (x:inner_metric_space hB) _)).
  exists r=>// y hy; apply:hBall.
  change (is_true (mdist (x+a:inner_metric_space hB) (y+a)<r)).
  by rewrite (@inner_translation_distance R V B hB a x y).
- have [r hr hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP
    (x:inner_metric_space hB) ((fun z:V=>z+a) @^-1` U)) hU.
  apply:(proj2 (metricType_numDomainType.nbhs_mdistP (x+a:inner_metric_space hB) U)).
  exists r=>// y hy.
  have hNear:mdist (x:inner_metric_space hB) (y-a)<r.
    by rewrite -(@inner_translation_distance R V B hB a x (y-a)) subrK.
  have hh:=hBall (y-a) hNear.
  change (U ((y-a)+a)) in hh; by rewrite subrK in hh.
Qed.
