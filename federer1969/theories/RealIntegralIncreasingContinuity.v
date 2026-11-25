(** Federer (1969), 2.5.1, p. 92: increasing convergence is preserved by the
    integral on a summable-function lattice, by 2.4.7, p. 84. Subtracting
    the first summable term reduces the signed statement to the nonnegative
    increasing-convergence theorem already proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialFunctionLimitExtremaUP PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIncreasingConvergence ExtendedRealOrderLimit SummableRealFunctionUP
  SummableRealArithmetic RealTotalIntegralLimits MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_integral_increasing_continuity]: direct
    increasing-continuity assertion of Federer 2.5.1, p. 92 The functions
    and their integrals may be signed; the limit is assumed summable. *)
Theorem real_integral_increasing_continuity (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> X -> R) (g : X -> R) (a : nat -> R) (b : R) :
  (forall n, is_measure_integral mu (real_total_integrand (f n)) (a n)%:E) ->
  is_measure_integral mu (real_total_integrand g) b%:E ->
  real_functions_increase_to f g -> extended_increases_to (fun n => (a n)%:E) b%:E.
Proof.
move=> hi hgi hinc.
pose v n x := (f n x-f 0%N x)%R.
pose w x := (g x-f 0%N x)%R.
have hv n := @real_total_integral_subtract R X mu hm (f n) (f 0%N) (a n) (a 0%N) (hi n) (hi 0%N).
have hw := @real_total_integral_subtract R X mu hm g (f 0%N) b (a 0%N) hgi (hi 0%N).
have hl : is_partial_function_lower_limit (fun n => real_total_integrand (v n)) (real_total_integrand w).
  apply: real_total_pointwise_lower_limit=> x.
  exact: (@real_order_limit_translate R (fun n => f n x) (g x) (-f 0%N x)%R (hinc x).2).
have hp n : measure_almost_everywhere mu (partial_extended_nonnegative_locus (real_total_integrand (v n))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (v n x)%:E; split; first by apply/real_total_integrand_graph.
  rewrite lee_fin /v subr_ge0.
  have hh := (hinc x).1 0%N n (leq0n n); by move: hh; rewrite lee_fin.
have hmon n : measure_almost_everywhere mu (partial_extended_le_locus (real_total_integrand (v n)) (real_total_integrand (v n.+1))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (v n x)%:E,(v n.+1 x)%:E; split; first by apply/real_total_integrand_graph.
  split; first by apply/real_total_integrand_graph.
  rewrite lee_fin /v lerD2r.
  have hh := (hinc x).1 n n.+1 (leqnSn n); by move: hh; rewrite lee_fin.
have hh := @measure_increasing_integral_values R X mu hm
  (fun n => real_total_integrand (v n)) (real_total_integrand w)
  (fun n => (a n-a 0%N)%R%:E) (b-a 0%N)%R%:E hl hp hmon hv hw.
split.
- move=> n k hnk; have h := hh.1 n k hnk.
  by move: h; rewrite !lee_fin lerD2r.
- have h := @real_order_limit_translate R (fun n => (a n-a 0%N)%R) (b-a 0%N)%R (a 0%N) hh.2.
  have he : (fun n => (a n-a 0%N+a 0%N)%R%:E)=(fun n => (a n)%:E).
    by apply: funext=> n; rewrite subrK.
  by rewrite he subrK in h.
Qed.
