(** Federer (1969), 3.4.5, p. 319: finite
    coordinate control for the exact jet metric, supporting
    its product topology and the compact growth-class proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal lra.
From Federer Require Import RealNormUP NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction NonnegativeSumScale
  BoundedDistanceScalar SequenceSpaceUP SequenceWeights SequenceMetricPrefixes
  JetSequenceMetricUP JetMetricWeights JetSequenceMetricExistence GeometricUniformTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_distance_scalar_le_input]: the
    normalized coordinate cost in 3.4.5, p. 319,
    is at most its nonnegative original norm distance. *)
Lemma bounded_distance_scalar_le_input (R:realType) (t:R):
  (0<=t)%R ->(bounded_distance_scalar t<=t)%R.
Proof.
move=>ht;have hDen:(0<1+t)%R by lra.
rewrite /bounded_distance_scalar ler_pdivrMr //.
have hSquare:(0<=t*t)%R:=mulr_ge0 ht ht.
rewrite mulrDr mulr1;by lra.
Qed.

(** Source for [jet_metric_weight_tail_bound]: the tail
    after the first K jet coordinates in 3.4.5,
    p. 319, has weight at most 2*2^(-K). *)
Lemma jet_metric_weight_tail_bound (R:realType) K:
  nonnegative_sum [set m|(K<=m)%N] (fun m=>(@jet_metric_weight R m)%:E)<=
    (2*@jet_metric_weight R K)%:E.
Proof.
have hTerms:nonnegative_sum [set m|(K<=m)%N] (fun m=>(@jet_metric_weight R m)%:E)=
    nonnegative_sum [set m|(K<=m)%N] (fun m=>(2:R)%:E*(@sequence_metric_weight R m)%:E).
  apply:nonnegative_sum_ext=>m _;by rewrite jet_metric_weight_positive_index EFinM.
rewrite hTerms nonnegative_sum_scale;last first.
- move=>m _;rewrite lee_fin;exact:ltW (sequence_metric_weight_positive m).
- by rewrite ler0n.
have hBound:=@sequence_metric_weight_tail R K.
have hTwo:0<=(2:R)%:E by rewrite lee_fin ler0n.
have hScaled:=lee_wpmul2l hTwo hBound.
by rewrite -EFinM in hScaled.
Qed.

Section FiniteControl.
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

(** Source for [jet_metric_finite_prefix_bound]: a finite
    prefix with norm differences at most delta has cost at
    most 2*delta; the remaining tail costs at most 2*2^(-K),
    3.4.5, p. 319. The tail retains all coordinates. *)
Lemma jet_metric_finite_prefix_bound (alpha beta:G) K (delta:R):
  (0<=delta)%R ->
  (forall m,(m<K)%N ->(N m (jet m alpha-jet m beta)<=delta)%R) ->
  (d alpha beta<=2*delta+2*jet_metric_weight K)%R.
Proof.
move=>hDelta hPrefix.
pose f m:=(jet_metric_weight m*bounded_distance_scalar (N m (jet m alpha-jet m beta)))%:E.
have hNonnegative m:0<=f m:=@jet_metric_term_nonnegative R G Z N hN jet alpha beta m.
have hHead:nonnegative_sum [set m|(m<K)%N] f<=(2*delta)%:E.
  have hEach m (hm:(m<K)%N):f m<=delta%:E*(@jet_metric_weight R m)%:E.
    rewrite /f -EFinM lee_fin (mulrC delta (jet_metric_weight m)).
    apply:ler_wpM2l;first exact:ltW (@jet_metric_weight_positive R m).
    exact:le_trans (bounded_distance_scalar_le_input (real_seminorm_nonnegative (hN m).1 _)) (hPrefix m hm).
  apply:le_trans (nonnegative_sum_mono hEach) _.
  rewrite nonnegative_sum_scale //;last by move=>m _;rewrite lee_fin;exact:ltW (@jet_metric_weight_positive R m).
  have hSubset:=@nonnegative_sum_subset R _ [set m|(m<K)%N] setT
    (fun m=>(@jet_metric_weight R m)%:E) (fun m hm=>Logic.I).
  have hBound:=le_trans hSubset (@jet_metric_weight_sum_bound R).
  have hDeltaE:0<=delta%:E by rewrite lee_fin.
  have hScaled:=lee_wpmul2l hDeltaE hBound.
  by rewrite -EFinM mulrC in hScaled.
have hTail:nonnegative_sum [set m|(K<=m)%N] f<=(2*@jet_metric_weight R K)%:E.
  apply:le_trans _ (@jet_metric_weight_tail_bound R K).
  apply:nonnegative_sum_mono=>m _;rewrite /f lee_fin.
  have hScalar:=bounded_distance_scalar_lt_one (real_seminorm_nonnegative (hN m).1 (jet m alpha-jet m beta)).
  have hCost:=ler_wpM2l (ltW (@jet_metric_weight_positive R m)) (ltW hScalar).
  by rewrite mulr1 in hCost.
have hComplement:setT `\` [set m|(m<K)%N]=[set m|(K<=m)%N].
  apply/seteqP;split.
  - move=>m [_ hm];rewrite /= leqNgt;apply/negP;exact:hm.
  - move=>m hm;split;first exact:Logic.I.
    move=>hLess;by rewrite /= leqNgt hLess in hm.
rewrite -lee_fin EFinD -(hd alpha beta).
change (nonnegative_sum setT f<=(2*delta)%:E+(2*jet_metric_weight K)%:E).
rewrite (@nonnegative_sum_split R _ setT [set m|(m<K)%N] f (fun m _=>hNonnegative m))
  setTI hComplement.
exact:leeD hHead hTail.
Qed.

(** Source for [jet_metric_finite_coordinate_control]: every
    positive metric tolerance in 3.4.5, p. 319,
    is enforced by finitely many sufficiently close derivative
    coordinates. Together with coordinate control this proves
    that the original metric gives the coefficient topology. *)
Theorem jet_metric_finite_coordinate_control (epsilon:R):
  (0<epsilon)%R ->exists K:nat,exists delta:R,(0<delta)%R /\
    forall alpha beta,(forall m,(m<K)%N ->(N m (jet m alpha-jet m beta)<delta)%R) ->
      (d alpha beta<epsilon)%R.
Proof.
move=>hEpsilon.
have hHalf:(0<(2^-1:R)<1)%R.
  apply/andP;split;first by rewrite invr_gt0 ltr0n.
  by rewrite invf_lt1 // ltr1n.
have hTwo:(0<=(2:R))%R by rewrite ler0n.
have hEpsilonHalf:(0<epsilon/2)%R by rewrite divr_gt0 // ltr0n.
have [K hK]:=@geometric_uniform_tail R (2^-1) 2 (epsilon/2) hHalf hTwo hEpsilonHalf.
pose delta:=(epsilon/8)%R.
have hDelta:(0<delta)%R by rewrite /delta divr_gt0 // ltr0n.
exists K,delta;split;first exact:hDelta.
move=>alpha beta hCoordinates.
have hBound:=@jet_metric_finite_prefix_bound alpha beta K delta (ltW hDelta)
  (fun m hm=>ltW (hCoordinates m hm)).
have hTail:=hK K (leqnn K).
rewrite [(_^+K*2)%R]mulrC -/(@jet_metric_weight R K) in hTail.
apply:le_lt_trans hBound _.
rewrite /delta;by lra.
Qed.
End FiniteControl.
