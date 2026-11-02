(** Federer (1969), 2.4.12, p. 87: continuity of the canonical linear
    embedding. Source context: ContinuousBidualUP.v. The abstract isometry
    gives a Lipschitz bound of one. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormMetricScaleContinuity
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP ContinuousBidualIsometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_bidual_continuous]: the continuity
    asserted for tau in Federer 2.4.12, p. 87, in the supplied norm topologies. *)
Theorem continuous_bidual_continuous (R : realType) (V D B : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom V B) : is_bidual_embedding ed eb tau ->
  continuous (fun y : real_norm_metric_space hN =>
    (tau y : real_norm_metric_space (continuous_dual_norm_is_norm hB))).
Proof.
move=> ht; apply: (@metric_fixed_lipschitz_continuous R
  [the metricType R of real_norm_metric_space hN]
  [the metricType R of real_norm_metric_space (continuous_dual_norm_is_norm hB)]
  (fun y => tau y) 1 ler01).
move=> x y; change (BN (tau x-tau y) <= 1*N (x-y)).
by rewrite -linearB (continuous_bidual_isometry hB ht) mul1r.
Qed.
