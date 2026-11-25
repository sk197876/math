(** Federer (1969), 3.4.5, p. 319: the exact
    jet metric controls each actual derivative coordinate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NonnegativeSum BoundedDistanceScalar JetSequenceMetricUP
  JetMetricWeights JetSequenceMetricExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CoordinateControl.
Variable R:realType.
Variable G:choiceType.
Variable Z:nat->lmodType R.
Variable N:forall m,Z m->R.
Arguments N m _ : clear implicits.
Hypothesis hN:forall m,is_real_norm (N m).
Variable jet:forall m,G->Z m.
Arguments jet m _ : clear implicits.
Variable d:G->G->R.
Hypothesis hd:is_jet_sequence_distance N jet d.

(** Source for [jet_metric_term_bound]: each weighted
    coordinate distance is bounded by the whole metric,
    3.4.5, p. 319. *)
Lemma jet_metric_term_bound (alpha beta:G) m:
  jet_metric_weight m*bounded_distance_scalar (N m (jet m alpha-jet m beta))<=d alpha beta.
Proof.
have hTerm:=@nonnegative_sum_term R _ setT
  (fun j=>(jet_metric_weight j*bounded_distance_scalar (N j (jet j alpha-jet j beta)))%:E) m Logic.I.
by rewrite (hd alpha beta) lee_fin in hTerm.
Qed.

(** Source for [jet_metric_coordinate_control]: continuity
    of each derivative coordinate for the exact metric of
    3.4.5, p. 319. A positive multiple of the
    bounded transform of epsilon is an explicit uniform cutoff. *)
Theorem jet_metric_coordinate_control m (epsilon:R):
  0<epsilon ->exists delta:R,0<delta /\forall alpha beta,
    d alpha beta<delta ->N m (jet m alpha-jet m beta)<epsilon.
Proof.
move=>hEpsilon.
have hDen:0<1+epsilon by exact:addr_gt0 ltr01 hEpsilon.
have hTransform:0<bounded_distance_scalar epsilon.
  exact:divr_gt0 hEpsilon hDen.
pose delta:=jet_metric_weight m*bounded_distance_scalar epsilon.
have hDelta:0<delta:=mulr_gt0 (@jet_metric_weight_positive R m) hTransform.
exists delta;split;first exact:hDelta.
move=>alpha beta hSmall;rewrite ltNge;apply/negP=>hLarge.
have hMonotone:=bounded_distance_scalar_monotone (ltW hEpsilon) hLarge.
have hWeighted:=ler_wpM2l (ltW (@jet_metric_weight_positive R m)) hMonotone.
have hLower:=le_trans hWeighted (jet_metric_term_bound alpha beta m).
by rewrite leNgt hSmall in hLower.
Qed.
End CoordinateControl.
