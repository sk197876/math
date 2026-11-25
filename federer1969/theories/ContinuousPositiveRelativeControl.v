(** Federer (1969), 3.2.46, pp. 281–282: a
    continuous positive density is locally controlled by
    arbitrary multiplicative factors above one. Supporting
    scalar-topology step in the printed localisation argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets topology.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_positive_relative_neighbourhood]:
    continuity at a positive value gives h(a)/lambda<=h(x)
    <=lambda h(a) on an actual open neighbourhood, supporting
    Federer 3.2.46, pp. 281–282. *)
Lemma continuous_positive_relative_neighbourhood (R : realType)
    (X : topologicalType) (h : X -> real_line_metric R) a (lambda : R) :
  continuous h -> 0<h a -> 1<lambda ->
  exists V : set X, open V /\ V a /\ forall x, V x ->
    h a/lambda<=h x /\ h x<=lambda*h a.
Proof.
move=> hCont ha hLambda.
have hLambda0 : 0<lambda := lt_trans ltr01 hLambda.
have hLambdaNe : lambda!=0 := lt0r_neq0 hLambda0.
pose e := (lambda-1)*h a/lambda.
have he : 0<e by rewrite /e divr_gt0 // mulr_gt0 // subr_gt0.
have hNb : nbhs (h a) [set y : real_line_metric R | `|h a-y|<e].
  apply: (metricType_numDomainType.nbhs_mdistP (h a) _).2.
  exists e=> // y hy; by rewrite -real_line_metric_distanceE.
have hPre := hCont a _ hNb.
rewrite nbhsE in hPre.
have [V [hV hVa] hControl] := hPre.
exists V; split; first exact hV; split; first exact hVa.
move=> x hx.
have hAbs := hControl x hx; change (is_true (`|h a-h x|<e)) in hAbs.
have /andP [hLower hUpper] : -e<h a-h x<e by rewrite -ltr_norml.
have hScale : e*lambda=(lambda-1)*h a by rewrite /e divfK.
have hCancel : (h a/lambda)*lambda=h a by rewrite divfK.
split; clear -hLower hUpper hScale hCancel hLambda ha he; nra.
Qed.
