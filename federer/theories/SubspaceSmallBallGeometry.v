(** Federer (1969), 4.1.5, p. 350:
    all sufficiently small balls about an
    interior point stay in the compact
    neighbourhood used for localization. The
    induced subspace balls have exactly the
    original ambient distance. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import MetricSubsetBackground MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [subspace_closed_ball_preimage]: the original
    ball intersected with U is the metric
    ball of the open subspace, supporting
    Federer 4.1.5, p. 350. *)
Lemma subspace_closed_ball_preimage (R:realType) (T:metricType R) (U:set T)
    (x:metric_subset U) (r:R):
  (fun y:metric_subset U=>set_val y) @^-1` metric_closed_ball (set_val x) r=
    metric_closed_ball x r.
Proof. reflexivity. Qed.

(** Source for [subspace_small_closed_ball_capture]: the
    actual neighbourhood margin for the compact
    localization in Federer 4.1.5, p. 350.
    A smaller closed ball lies inside the
    original neighbourhood, without properness assumptions. *)
Lemma subspace_small_closed_ball_capture (R:realType) (T:metricType R)
    (U C:set T) (x:metric_subset U):
  interior C (set_val x) ->exists cap:R,0<cap /\forall r:R,0<r ->r<cap ->
    metric_closed_ball (set_val x) r `<=` C.
Proof.
move=>hInterior.
have[d hD hBall]:=(metricType_numDomainType.nbhs_mdistP (set_val x) C).1 hInterior.
exists (d/2); split; first by rewrite divr_gt0 // ltr0n.
move=>r hR hSmall y hY.
apply:hBall; have hDistance:mdist (set_val x) y<=r:=hY.
change (is_true (mdist (set_val x) y<d)).
have hPositiveD:0<d:=hD.
lra.
Qed.
