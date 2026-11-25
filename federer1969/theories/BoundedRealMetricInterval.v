(** Federer (1969), 3.2.6, p. 245: a bounded
    source set lies in a nondegenerate compact interval.
    Use the existing abstract finite-diameter specification;
    the empty set is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology MetricDiameterUP MetricDiameter CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_real_metric_interval_exists]: supporting
    compact-interval localization of the bounded set A in
    Federer 3.2.6, pp. 245–246. The bound is the
    already specified diameter; no extremum of A is assumed. *)
Lemma bounded_real_metric_interval_exists (R:realType) (A:set (real_line_metric R)):
  metric_set_bounded A -> exists a b:R,a<b /\ A `<=` `[a,b].
Proof.
move=>hBound; case:(pselect (exists x,A x))=>hNonempty.
- have [c hc]:=hNonempty.
  pose D:=@extended_metric_diameter R [the metricType R of real_line_metric R] A.
  have hD:=@extended_metric_diameter_specification R [the metricType R of real_line_metric R] A.
  have hNum:D \is a fin_num.
    rewrite (ge0_fin_numE (metric_diameter_nonnegative hD)); exact hBound.
  have hRep:D=(fine D)%:E:=esym (fineK hNum).
  have hFine:0<=fine D.
    have hn:=metric_diameter_nonnegative hD; by rewrite -/D hRep lee_fin in hn.
  pose r:=fine D+1.
  have hr:0<r by rewrite /r; lra.
  exists (c-r),(c+r); split; first by lra.
  move=>x hx.
  have hPair:=metric_diameter_upper hD hx hc.
  change (is_true ((mdist (x:real_line_metric R) c)%:E<=D)%E) in hPair.
  rewrite real_line_metric_distanceE hRep lee_fin in hPair.
  have hPlus:x-c<=`|x-c| :=ler_norm (x-c).
  have hMinus:c-x<=`|x-c| by rewrite distrC; exact:ler_norm.
  rewrite /= in_itv /=; apply/andP; split; rewrite /r; lra.
- exists (-1),1; split; first by lra.
  move=>x hx; exfalso; apply:hNonempty; by exists x.
Qed.
