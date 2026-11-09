(** Federer (1969), 3.4.5, p. 319: metric
    laws follow from the exact jet-series specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NonnegativeSum NonnegativeSumSupport NonnegativeSumAdd
  BoundedDistanceScalar JetSequenceMetricUP JetMetricWeights JetSequenceMetricExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section MetricLaws.
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

(** Source for [jet_sequence_distance_self]: the displayed
    distance of a germ from itself is zero, 3.4.5, p. 319. *)
Lemma jet_sequence_distance_self alpha:d alpha alpha=0%R.
Proof.
apply/eqP;rewrite -eqe -(hd alpha alpha);apply/eqP.
apply:nonnegative_sum_zero=>m _.
by rewrite subrr (real_seminorm_zero (hN m).1) bounded_distance_scalar_zero mulr0.
Qed.

(** Source for [jet_sequence_distance_symmetric]: symmetry
    of the displayed distance, 3.4.5, p. 319. *)
Lemma jet_sequence_distance_symmetric alpha beta:d alpha beta=d beta alpha.
Proof.
apply/eqP;rewrite -eqe -(hd alpha beta) -(hd beta alpha);apply/eqP.
apply:nonnegative_sum_ext=>m _.
by rewrite (real_seminorm_subtract (hN m).1 (jet m alpha) (jet m beta)).
Qed.

(** Source for [jet_sequence_distance_triangle]: triangle
    inequality for the displayed metric, 3.4.5, p. 319.
    Apply the proved monotone subadditive transform t/(1+t)
    to each norm distance, then sum its weighted inequalities. *)
Lemma jet_sequence_distance_triangle alpha beta gamma:
  (d alpha gamma<=d alpha beta+d beta gamma)%R.
Proof.
rewrite -lee_fin EFinD -(hd alpha gamma) -(hd alpha beta) -(hd beta gamma).
rewrite -nonnegative_sum_add;last first.
- move=>m _;exact:(@jet_metric_term_nonnegative R G Z N hN jet beta gamma m).
- move=>m _;exact:(@jet_metric_term_nonnegative R G Z N hN jet alpha beta m).
apply:nonnegative_sum_mono=>m _;rewrite -EFinD lee_fin -mulrDr.
apply:ler_wpM2l;first exact:ltW (@jet_metric_weight_positive R m).
apply:le_trans _ (bounded_distance_scalar_subadditive
  (real_seminorm_nonnegative (hN m).1 _) (real_seminorm_nonnegative (hN m).1 _)).
apply:bounded_distance_scalar_monotone.
- exact:(real_seminorm_nonnegative (hN m).1 (jet m alpha-jet m gamma)).
have hDifference:(jet m alpha-jet m gamma)%R=
    ((jet m alpha-jet m beta)+(jet m beta-jet m gamma))%R by rewrite addrA subrK.
rewrite hDifference;exact:(real_seminorm_triangle (hN m).1 (jet m alpha-jet m beta) (jet m beta-jet m gamma)).
Qed.

(** Source for [jet_sequence_distance_separates]: zero
    distance forces equality of every actual derivative,
    3.4.5, p. 319. Derivative injectivity then gives
    equality of the original germs; no metric separation is assumed. *)
Lemma jet_sequence_distance_separates:
  (forall alpha beta,(forall m,jet m alpha=jet m beta) ->alpha=beta) ->
  forall alpha beta,d alpha beta=0%R ->alpha=beta.
Proof.
move=>hInjective alpha beta hZero;apply:hInjective=>m.
have hSum:nonnegative_sum setT (fun j=>
    (jet_metric_weight j*bounded_distance_scalar (N j (jet j alpha-jet j beta)))%:E)=0.
  by rewrite (hd alpha beta) hZero.
have hTerm:=proj1 (nonnegative_sum_zero_iff
  (fun j _=>@jet_metric_term_nonnegative R G Z N hN jet alpha beta j)) hSum m Logic.I.
move/eqP:hTerm;rewrite eqe mulf_eq0 (gt_eqF (@jet_metric_weight_positive R m)) orFb
  bounded_distance_scalar_eq_zero;last exact:(real_seminorm_nonnegative (hN m).1 (jet m alpha-jet m beta)).
move/eqP=>hNorm.
have hDifference:=((hN m).2 (jet m alpha-jet m beta)%R hNorm).
by move/eqP:hDifference;rewrite subr_eq0=>/eqP.
Qed.

(** Source for [jet_sequence_distance_unique]: the exact
    series determines the real distance uniquely, 3.4.5, p. 319. *)
Lemma jet_sequence_distance_unique (e:G->G->R):
  is_jet_sequence_distance N jet e ->d=e.
Proof.
move=>he;apply:funext=>alpha;apply:funext=>beta.
apply/eqP;rewrite -eqe -(hd alpha beta) -(he alpha beta);exact:eqxx.
Qed.
End MetricLaws.
