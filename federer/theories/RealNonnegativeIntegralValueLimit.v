(** Federer (1969), 3.2.13, p. 250: supporting total-real
    adapter for the increasing convergence theorem 2.4.7, p. 84,
    applied to the bounded square-substitution integrals. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP SummableRealFunctionUP MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP PartialExtendedOrderLoci
  MeasureIncreasingConvergence ExtendedRealOrderLimit RealTotalIntegralLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_nonnegative_integral_value_limit]: the
    integral values of nonnegative increasing real functions converge
    to the integral of their pointwise limit, Federer 2.4.7,
    p. 84, used in 3.2.13, p. 250. The intermediate
    integral values may be extended real. *)
Lemma real_nonnegative_integral_value_limit (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (f:nat->X->R) (g:X->R)
    (a:nat->\bar R) b:
  (forall n x,0<=f n x) ->
  (forall n x,f n x<=f n.+1 x) ->
  (forall x,extended_order_limit (fun n=>(f n x)%:E) (g x)%:E) ->
  (forall n,is_measure_integral mu (real_total_integrand (f n)) (a n)) ->
  is_measure_integral mu (real_total_integrand g) b ->extended_order_limit a b.
Proof.
move=>hp hmon hconv hi hgi.
have hg:=real_total_pointwise_lower_limit hconv.
have hpos n:measure_almost_everywhere mu
    (partial_extended_nonnegative_locus (real_total_integrand (f n))).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=>x _.
  exists (f n x)%:E; split; first exact/real_total_integrand_graph.
  by rewrite lee_fin; exact:hp.
have hinc n:measure_almost_everywhere mu
    (partial_extended_le_locus (real_total_integrand (f n)) (real_total_integrand (f n.+1))).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=>x _.
  exists (f n x)%:E,(f n.+1 x)%:E; split; first exact/real_total_integrand_graph.
  split; first exact/real_total_integrand_graph.
  by rewrite lee_fin; exact:hmon.
exact:(@measure_increasing_integral_values R X mu hm
  (fun n=>real_total_integrand (f n)) (real_total_integrand g) a b hg hpos hinc hi hgi).2.
Qed.
