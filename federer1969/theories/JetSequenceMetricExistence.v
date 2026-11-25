(** Federer (1969), 3.4.5, p. 319: existence
    of the exact finite real jet distance. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP NonnegativeSum NonnegativeSumSupport BoundedDistanceScalar
  JetSequenceMetricUP JetMetricWeights.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section DistanceExistence.
Variable R:realType.
Variable G:choiceType.
Variable Z:nat->lmodType R.
Variable N:forall m,Z m->R.
Arguments N m _ : clear implicits.
Hypothesis hN:forall m,is_real_norm (N m).
Variable jet:forall m,G->Z m.
Arguments jet m _ : clear implicits.

(** Source for [jet_metric_term_nonnegative]: every summand
    in the exact displayed distance is nonnegative,
    3.4.5, p. 319. *)
Lemma jet_metric_term_nonnegative (alpha beta:G) m:
  0<=(jet_metric_weight m*bounded_distance_scalar (N m (jet m alpha-jet m beta)))%:E.
Proof.
rewrite lee_fin;apply:mulr_ge0;first exact:ltW (@jet_metric_weight_positive R m).
exact:bounded_distance_scalar_nonnegative (real_seminorm_nonnegative (hN m).1 _).
Qed.

(** Source for [jet_metric_series_bound]: the exact series
    of 3.4.5, p. 319, has a finite real value,
    bounded by two. This is proved before defining its distance. *)
Lemma jet_metric_series_bound (alpha beta:G):
  0<=nonnegative_sum setT (fun m=>
    (jet_metric_weight m*bounded_distance_scalar (N m (jet m alpha-jet m beta)))%:E) /\
  nonnegative_sum setT (fun m=>
    (jet_metric_weight m*bounded_distance_scalar (N m (jet m alpha-jet m beta)))%:E)<=2%:E.
Proof.
split;first exact:nonnegative_sum_nonnegative.
apply:le_trans _ (@jet_metric_weight_sum_bound R).
apply:nonnegative_sum_mono=>m _;rewrite lee_fin.
have hTransform:=bounded_distance_scalar_lt_one (real_seminorm_nonnegative (hN m).1 (jet m alpha-jet m beta)).
have hBound:=ler_wpM2l (ltW (@jet_metric_weight_positive R m)) (ltW hTransform).
by rewrite mulr1 in hBound.
Qed.

(** Source for [jet_sequence_distance_exists]: existence of
    a distance satisfying the exact independent series formula
    in 3.4.5, p. 319. No metric theorem is assumed. *)
Theorem jet_sequence_distance_exists:exists d:G->G->R,is_jet_sequence_distance N jet d.
Proof.
exists (fun alpha beta=>fine (nonnegative_sum setT (fun m=>
  (jet_metric_weight m*bounded_distance_scalar (N m (jet m alpha-jet m beta)))%:E))).
move=>alpha beta;apply:esym;apply:fineK.
have [hZero hBound]:=jet_metric_series_bound alpha beta.
rewrite ge0_fin_numE //;exact:le_lt_trans hBound (ltry _).
Qed.
End DistanceExistence.
