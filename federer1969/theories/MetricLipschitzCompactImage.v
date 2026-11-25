(** General metric topology supporting Federer (1969), 2.2.7,
    pp. 63–64, and the compact coordinate cores used
    in 3.2.47, p. 283. The Lipschitz bound is
    needed only on the actual compact source set. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import LipschitzUP NormMetricScaleContinuity MetricSubsetBackground CompactMetricSubset.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [metric_lipschitz_compact_image]: Lipschitz
    maps are continuous on their actual domains, by
    2.2.7, pp. 63–64; general topology makes
    compact images compact. Supporting the two chart bounds
    in 3.2.47, p. 283, without a global extension. *)
Theorem metric_lipschitz_compact_image (R:realType) (X Y:metricType R)
    (K:set X) (f:X->Y):
  @compact X K ->is_metric_lipschitz K f ->@compact Y (f @` K).
Proof.
move=>hK [L [_ hBound]].
pose F:=fun x:metric_subset K=>f (val x).
have hContinuous:continuous F.
  apply:(@metric_fixed_lipschitz_continuous R (metric_subset K) Y F L hBound.1).
  move=>x y; rewrite metric_subset_distanceE.
  exact (hBound.2 (val x) (val y) (set_valP x) (set_valP y)).
have hImage:=continuous_compact (continuous_subspaceT hContinuous) (compact_metric_subset_whole hK).
have hEq:F @` setT=f @` K.
  apply/seteqP; split=>y.
  - move=>[x _ <-]; exists (val x); first exact (set_valP x).
    reflexivity.
  - move=>[x hx <-]; exists (Sub x (mem_set hx):metric_subset K); first exact I.
    reflexivity.
by rewrite hEq in hImage.
Qed.
