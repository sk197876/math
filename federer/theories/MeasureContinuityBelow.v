(** Federer (1969), 2.1.3(4), p. 55: continuity along increasing measurable
    sets. The proof follows the disjoint-increment reduction in Federer;
    convergence is in the extended order topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumContinuity
  ExtendedRealOrderLimit MeasureUP MeasureBasic MeasureCountableAdditivity
  SetSequenceDisjointification MeasureSequencePrefixes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_continuity_below]: Federer 2.1.3(4), p. 55; measures
    of increasing measurable sets converge increasingly to the measure of
    their union, without a finiteness hypothesis. *)
Theorem measure_continuity_below (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (F : nat -> set I) :
  (forall n, measure_measurable mu (F n)) ->
  (forall n m, (n <= m)%N -> F n `<=` F m) ->
  extended_increases_to (fun n => mu (F n)) (mu (\bigcup_n F n)).
Proof.
move=> hF hmono.
have hD := (@measure_sequence_disjointify_measurable R I mu hm F hF).
have hs := @measure_sequence_disjoint_additivity R I mu hm
  (set_sequence_disjointify F) hD (@set_sequence_disjointify_disjoint I F).
rewrite set_sequence_disjointify_union in hs.
have he : (fun n => mu (F n)) = (fun n => nonnegative_sum
    [set k | (k < n.+1)%N] (fun k => mu (set_sequence_disjointify F k))).
  apply: funext=> n.
  rewrite -(@set_sequence_prefix_increasing I F hmono n).
  exact: (@measure_sequence_disjointify_prefix_sum R I mu hm F hF n.+1).
rewrite he hs; apply: nonnegative_sum_increasing_limit.
- move=> n m hnm k hk; exact: leq_trans hk (leq_ltn_trans hnm (ltnSn m)).
- by move=> n k _.
- move=> k _; exists k; exact: ltnSn.
Qed.
