(** Federer (1969), 2.5.7, p. 98: the bounded increasing limit of
    nonnegative Lq densities has an Lq representative. This is the analytic
    closure step; domination of pairings is proved separately. The norm
    bound includes q=infinity without assuming that X is countably
    measurable. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionLimitUP MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP ExtendedRealOrderLimit ExtendedRealBoundsUP
  ExtendedIncreasingLimitSupremum TotalScalarLpUP TotalExtendedLowerLimit RealLowerLimitReplacement
  FiniteLpLowerLimitFiniteness InfinityLowerLimitFiniteness TotalScalarLpLowerSemicontinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_lp_lower_limit_almost_finite]: the two
    almost-finiteness arguments for the candidate limit in Federer 2.5.7, p.
    98 All admissible exponents, including one and infinity, are covered. *)
Lemma bounded_lp_lower_limit_almost_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q : \bar R) (M : R) (u : nat -> X -> R) :
  (forall n, total_scalar_lp mu q (u n)) ->
  (forall n x, (0 <= u n x)%R) ->
  (forall n, total_scalar_lp_norm mu q (u n) <= M%:E) ->
  measure_almost_everywhere mu
    [set x | total_extended_lower_limit (fun n x => (u n x)%:E) x \is a fin_num].
Proof.
case: q=> [q| |] hu hu0 hb.
- exact: (@finite_lp_bounded_lower_limit_almost_finite R X mu hm q M u hu hu0 hb).
- exact: (@infinity_bounded_lower_limit_almost_finite R X mu hm M u (fun n => (hu n).2.1) hu0 hb).
- by have hh := (hu 0%N).1.
Qed.

(** Source for [bounded_increasing_lp_replacement]: the actual Lq
    representative of the increasing sequence in Federer 2.5.7, p. 98 Both
    its norm bound and its countably measurable support are conclusions. *)
Theorem bounded_increasing_lp_replacement (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q : \bar R) (M : R) (u : nat -> X -> R) :
  (forall n, total_scalar_lp mu q (u n)) ->
  (forall n x, (0 <= u n x)%R) ->
  (forall n m x, (n <= m)%N -> (u n x <= u m x)%R) ->
  (forall n, total_scalar_lp_norm mu q (u n) <= M%:E) ->
  total_scalar_lp mu q (real_lower_limit_replacement u) /\
  (forall x, (0 <= real_lower_limit_replacement u x)%R) /\
  total_scalar_lp_norm mu q (real_lower_limit_replacement u) <= M%:E /\
  measure_almost_everywhere mu [set x | extended_increases_to
    (fun n => (u n x)%:E) (real_lower_limit_replacement u x)%:E].
Proof.
move=> hu hu0 hinc hb.
have hf := @bounded_lp_lower_limit_almost_finite R X mu hm q M u hu hu0 hb.
have hg := @real_lower_limit_replacement_measurable R X mu hm u (fun n => (hu n).2.1).
have hc := @real_lower_limit_replacement_countable_support R X mu hm u (fun n => (hu n).2.2.2).
have hl := @real_lower_limit_replacement_converges R X mu hm u hinc hf.
have hnorm := @total_scalar_lp_limit_uniform_bound R X mu hm q u _ M (hu 0%N).1
  (fun n => (hu n).2.1) hg hl hb.
split.
- split; first exact: (hu 0%N).1.
  split=> //; split=> //; exact: le_lt_trans hnorm (ltry M).
- split; first exact: real_lower_limit_replacement_nonnegative hu0.
  split=> //; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hf)=> x hx.
  change (extended_increases_to (fun n => (u n x)%:E)
    (fine (total_extended_lower_limit (fun n x => (u n x)%:E) x))%:E).
  rewrite (fineK hx); apply: total_extended_lower_limit_increases.
  by move=> n m y hnm; rewrite lee_fin; exact: hinc.
Qed.

(** Source for [bounded_increasing_lp_upper_representative]: every
    approximant lies below the representative almost everywhere, supporting
    the maximal-density argument in Federer 2.5.7, pp. 98–99 One common
    conull set works for every sequence index. *)
Lemma bounded_increasing_lp_upper_representative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q : \bar R) (M : R) (u : nat -> X -> R) :
  (forall n, total_scalar_lp mu q (u n)) ->
  (forall n x, (0 <= u n x)%R) ->
  (forall n m x, (n <= m)%N -> (u n x <= u m x)%R) ->
  (forall n, total_scalar_lp_norm mu q (u n) <= M%:E) ->
  measure_almost_everywhere mu [set x | forall n, (u n x <= real_lower_limit_replacement u x)%R].
Proof.
move=> hu hu0 hinc hb.
have hl := (@bounded_increasing_lp_replacement R X mu hm q M u hu hu0 hinc hb).2.2.2.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hl)=> x hx n.
have hh : (u n x)%:E <= (real_lower_limit_replacement u x)%:E.
  apply: (extended_real_supremum_upper (extended_increasing_limit_supremum hx)); by exists n.
by rewrite lee_fin in hh.
Qed.
