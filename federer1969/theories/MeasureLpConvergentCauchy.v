(** Federer (1969), 2.4.12, pp. 87–88: supporting Cauchy property of
    approximants in the finite-p seminorm. This is used in extending the
    integral from finite-image functions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasurableNormedFunctionUP
  MeasureLpConvergence MeasureLpDistanceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convergent_in_lp_norm_cauchy]: supporting Cauchy
    inference for the vector-integral extension in Federer 2.4.12,
    pp. 87–88. A common limit controls both sides by half the error. *)
Lemma convergent_in_lp_norm_cauchy (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (h : partial_function X (real_norm_metric_space hN)) :
  (1 <= p)%R -> (forall n, is_measurable_normed_function mu (f n)) ->
  is_measurable_normed_function mu h -> converges_in_lp_norm mu N p f h ->
  cauchy_in_lp_norm mu N p f.
Proof.
move=> hp hf hh hl e he.
have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
have [K hK] := hl _ he2; exists K=> n m hn hm'.
have ht := @measure_lp_distance_triangle R X V N hN mu hm p (f n) h (f m)
  hp (hf n) hh (hf m).
rewrite (@measure_lp_distance_symmetric R X V N hN mu hm p h (f m) hp hh (hf m)) in ht.
apply: le_lt_trans ht _.
have hsum := lteD (hK n hn) (hK m hm').
by rewrite -EFinD -splitr in hsum.
Qed.
