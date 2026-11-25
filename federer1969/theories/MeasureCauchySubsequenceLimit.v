(** Federer (1969), 2.3.10, p. 80: the limit of a convergent subsequence is
    the limit of the entire Cauchy sequence, giving the printed completeness
    conclusion. This elementary triangle argument is explicit here for the
    extended pseudodistance. Source context: CauchyIndexSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP
  MeasurableNormedFunctionUP MeasureConvergenceUP MeasureDistanceLaws CauchyIndexSelectionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [cauchy_measure_subsequence_limit]: supporting
    final completeness inference in Federer 2.3.10, p. 80.
    Finite epsilon bounds make the triangle argument valid even
    though unrestricted distances can be infinite. *)
Lemma cauchy_measure_subsequence_limit (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (h : partial_function X (real_norm_metric_space hN)) (s : nat -> nat) :
  (forall n, is_measurable_normed_function mu (f n)) ->
  is_measurable_normed_function mu h -> cauchy_in_measure mu N f ->
  (forall n, (s n < s n.+1)%N) ->
  converges_in_measure mu N (fun n => f (s n)) h -> converges_in_measure mu N f h.
Proof.
move=> hf hh hc hs hl e he.
have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
have [K hK] := hc _ he2; have [L hL] := hl _ he2.
exists K=> n hn; pose k := maxn K L.
have hk : (K <= s k)%N.
  exact: leq_trans (leq_maxl K L) (strict_index_sequence_dominates hs k).
have h1 := hK n (s k) hn hk.
have h2 := hL k (leq_maxr K L).
have ht := @measure_normed_distance_triangle R X V N hN mu hm (f n) (f (s k)) h
  (hf n) (hf (s k)) hh.
apply: le_lt_trans ht _.
have hsum := lteD h1 h2.
by rewrite -EFinD -splitr in hsum.
Qed.
