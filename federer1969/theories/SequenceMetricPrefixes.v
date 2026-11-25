(** Federer (1969), 2.2.6, p. 63: estimates relating the metric to finite
    coordinate agreement. These local estimates provide their quantitative
    ingredients. Source context and index encoding: SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction
  GeometricErrorBudget PositiveIntegerDistance SequenceSpaceUP SequenceWeights SequenceMetricLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sequence_metric_weight_prefix]: Federer
    2.2.6, p. 63, supporting finite geometric identity: the
    first N metric weights have sum 1-2^-N, including N=0. *)
Lemma sequence_metric_weight_prefix (R : realType) N :
  nonnegative_sum [set i | (i < N)%N] (fun i => (@sequence_metric_weight R i)%:E) =
    (1 - (2^-1)^+N)%:E.
Proof.
have he : nonnegative_sum [set i | (i < N)%N] (fun i => (@sequence_metric_weight R i)%:E) =
    nonnegative_sum [set i | (i < N)%N] (fun i => (geometric_error_budget (2 : R)%R i)%:E).
  apply: nonnegative_sum_ext=> i _; by rewrite sequence_metric_weight_as_budget.
have hp : (0 < (2 : R))%R by rewrite ltr0n.
rewrite he (geometric_error_prefix_sum N hp) /geometric_error_tail.
by rewrite divff ?pnatr_eq0 // !mul1r expr0.
Qed.

(** Source for [sequence_metric_weight_tail]: Federer
    2.2.6, p. 63, supporting tail bound: weights after the
    first N coordinates have total at most 2^-N. This follows
    from the unit bound and the exact finite prefix, by finite
    cancellation in the extended reals. *)
Lemma sequence_metric_weight_tail (R : realType) N :
  nonnegative_sum [set i | (N <= i)%N] (fun i => (@sequence_metric_weight R i)%:E) <=
    ((2^-1)^+N)%:E.
Proof.
have hnon i : 0 <= (@sequence_metric_weight R i)%:E.
  rewrite lee_fin; exact: ltW (sequence_metric_weight_positive i).
have hsplit := @nonnegative_sum_split R _ setT [set i | (i < N)%N]
  (fun i => (@sequence_metric_weight R i)%:E) (fun i _ => hnon i).
have hd : setT `\` [set i | (i < N)%N] = [set i | (N <= i)%N].
  apply/seteqP; split.
  - move=> i [_ hn]; rewrite /= leqNgt; apply/negP; exact hn.
  - move=> i hi; split; first exact Logic.I.
    move=> hlt; by move: hi; rewrite /= leqNgt hlt.
have hb := @sequence_metric_weight_sum_bound R.
rewrite hsplit setTI hd sequence_metric_weight_prefix in hb.
have he : (1 : \bar R) = (1 - (2^-1)^+N)%:E + ((2^-1)^+N)%:E.
  by rewrite -EFinD subrK.
by rewrite he leeD2lE // in hb.
Qed.

(** Source for [positive_sequence_prefix_distance_bound]: Federer 2.2.6, p.
    63, supporting product-topology estimate: sequences agreeing on the
    first N coordinates have distance at most 2^-N. The first N summands
    vanish and the remaining ones are bounded by the geometric tail. *)
Lemma positive_sequence_prefix_distance_bound (R : realType) (S : choiceType)
    (coordinate : S -> nat -> nat) (d : S -> S -> R)
    (hd : is_positive_sequence_metric coordinate d) x y N :
  (forall i, (i < N)%N -> coordinate x i = coordinate y i) ->
  (d x y <= (2^-1)^+N)%R.
Proof.
move=> hcoord; rewrite -lee_fin -(hd x y).
have h0 : nonnegative_sum (setT `&` [set i | (i < N)%N]) (fun i =>
    (@sequence_metric_weight R i * positive_integer_distance (coordinate x i) (coordinate y i))%:E) = 0.
  apply: nonnegative_sum_zero=> i [_ hi].
  by rewrite (hcoord i hi) positive_integer_distance_self mulr0.
have hdom : setT `\` [set i | (i < N)%N] = [set i | (N <= i)%N].
  apply/seteqP; split.
  - move=> i [_ hn]; rewrite /= leqNgt; apply/negP; exact hn.
  - move=> i hi; split; first exact Logic.I.
    move=> hlt; by move: hi; rewrite /= leqNgt hlt.
rewrite (@nonnegative_sum_split R _ setT [set i | (i < N)%N]) //.
- rewrite h0 hdom add0e; apply: le_trans _ (@sequence_metric_weight_tail R N).
  apply: nonnegative_sum_mono=> i hi.
  rewrite lee_fin -{2}[@sequence_metric_weight R i]mulr1.
  apply: ler_wpM2l; first exact: ltW (sequence_metric_weight_positive i).
  exact: ltW (positive_integer_distance_lt_one (coordinate x i) (coordinate y i)).
- move=> i _; exact: sequence_metric_term_nonnegative.
Qed.

(** Source for [positive_sequence_small_distance_coordinate]: Federer 2.2.6,
    p. 63, supporting converse product-topology estimate: distance smaller
    than half the ith weight forces equality of that coordinate. Distinct
    integer coordinates have normalised gap at least one half. *)
Lemma positive_sequence_small_distance_coordinate (R : realType) (S : choiceType)
    (coordinate : S -> nat -> nat) (d : S -> S -> R)
    (hd : is_positive_sequence_metric coordinate d) x y i :
  (d x y < sequence_metric_weight i / 2)%R -> coordinate x i = coordinate y i.
Proof.
move=> hlt; have [hsame|hn] := boolP (coordinate x i == coordinate y i).
  exact/eqP.
exfalso;
have hgap := @positive_integer_distance_gap R _ _ hn.
have hterm := @nonnegative_sum_term R _ setT
  (fun j => (@sequence_metric_weight R j * positive_integer_distance (coordinate x j) (coordinate y j))%:E) i Logic.I.
rewrite (hd x y) lee_fin in hterm.
have hlow : (sequence_metric_weight i / 2 <= d x y)%R.
  have hmul : (@sequence_metric_weight R i * (1 / 2) <=
      sequence_metric_weight i * positive_integer_distance (coordinate x i) (coordinate y i))%R.
    apply: ler_wpM2l; first exact: ltW (@sequence_metric_weight_positive R i).
    exact hgap.
  rewrite mulrA mulr1 in hmul.
  exact: le_trans hmul hterm.
by move: hlt; rewrite ltNge hlow.
Qed.
