(** Federer (1969), 3.4.5, p. 319: the
    positive jet-metric weights have sum at most two. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumScale SequenceSpaceUP SequenceWeights JetSequenceMetricUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [jet_metric_weight_positive]: every coordinate
    coefficient of the exact metric is positive, 3.4.5, p. 319. *)
Lemma jet_metric_weight_positive (R:realType) m:(0<@jet_metric_weight R m)%R.
Proof. by rewrite /jet_metric_weight exprn_gt0 // invr_gt0 ltr0n. Qed.

(** Source for [jet_metric_weight_positive_index]: the
    zero-based coefficient of 3.4.5, p. 319, is
    twice the positive-index coefficient of 2.2.6, p. 63. *)
Lemma jet_metric_weight_positive_index (R:realType) m:
  @jet_metric_weight R m=(2*@sequence_metric_weight R m)%R.
Proof.
rewrite /jet_metric_weight /sequence_metric_weight exprSr mulrCA.
by rewrite mulfV ?pnatr_eq0 // mulr1.
Qed.

(** Source for [jet_metric_weight_sum_bound]: summability
    of the exact coefficients in 3.4.5, p. 319,
    from the already proved local geometric-series bound. *)
Theorem jet_metric_weight_sum_bound (R:realType):
  nonnegative_sum setT (fun m=>(@jet_metric_weight R m)%:E)<=2%:E.
Proof.
have hTerms:nonnegative_sum setT (fun m=>(@jet_metric_weight R m)%:E)=
    nonnegative_sum setT (fun m=>(2:R)%:E*(@sequence_metric_weight R m)%:E).
  apply:nonnegative_sum_ext=>m _;by rewrite jet_metric_weight_positive_index EFinM.
rewrite hTerms nonnegative_sum_scale;last first.
- move=>m _;rewrite lee_fin;exact:ltW (sequence_metric_weight_positive m).
- by rewrite ler0n.
have hBound:=@sequence_metric_weight_sum_bound R.
have hTwo:0<=(2:R)%:E by rewrite lee_fin ler0n.
have hScaled:=lee_wpmul2l hTwo hBound.
by rewrite mule1 in hScaled.
Qed.
