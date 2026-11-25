(** Federer (1969), 3.2.46, p. 281: an escaping curve
    has both a first exit and a last return, with the two
    endpoint collars lying in the comparison region. This
    supporting scalar fact uses actual continuity and level hits. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring
  classical_sets topology.
From Federer Require Import RealMetricBackground ContinuousFirstLevelCrossing
  NormedCurveParameterReflection RealDerivativeContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_two_level_crossings]: supporting
    both controlled collars in the lower distance comparison
    of Federer 3.2.46, p. 281. The original intervening
    interval is retained; no containment of that middle
    curve segment is asserted. *)
Lemma continuous_two_level_crossings (R : realType) (f : R -> R) a b q r :
  continuous (f : real_line_metric R -> real_line_metric R) ->
  a <= q <= b -> f a < r -> r < f q -> f b < r ->
  exists u v : R, a < u < q /\ q < v < b /\
    f u = r /\ f v = r /\
    (forall t, a <= t <= u -> f t <= r) /\
    (forall t, v <= t <= b -> f t <= r).
Proof.
move=> hf /andP [haq hqb] hfa hfq hfb.
have [u [hu [hValue hPrefix]]] := @continuous_first_level_crossing R f a q r
  haq (continuous_subspaceT hf) hfa hfq.
pose F := fun t : real_line_metric R=>f (a+b-t).
have hReflection : continuous (fun t : real_line_metric R => (a+b-t : real_line_metric R)).
  move=> t; exact: real_derivative_continuous_at (scalar_reflection_actual_derivative (a+b) t).
have hF : continuous (F : real_line_metric R -> real_line_metric R).
  move=> t; exact: continuous_comp (hReflection t) (hf (a+b-t)).
have hFirst : a+b-a=b by ring.
have hInv t : a+b-(a+b-t)=t by ring.
have hAq : a <= a+b-q by lra.
have hFStart : F a < r by rewrite /F hFirst.
have hFEnd : r < F (a+b-q) by rewrite /F hInv.
have [w [hw [hWValue hWPrefix]]] := @continuous_first_level_crossing R F a (a+b-q) r
  hAq (continuous_subspaceT hF) hFStart hFEnd.
pose v := a+b-w.
have hv : q < v < b.
  have /andP [haw hwq] := hw; rewrite /v; apply/andP; split; lra.
exists u,v; split; first exact hu; split; first exact hv.
split; first exact hValue; split; first exact hWValue.
split; first exact hPrefix.
move=> t /andP [hvt htb].
have hTime : a <= a+b-t <= w.
  rewrite /v in hvt; apply/andP; split; lra.
have hBound := hWPrefix (a+b-t) hTime.
by rewrite /F hInv in hBound.
Qed.
