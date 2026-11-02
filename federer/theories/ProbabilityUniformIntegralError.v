(** Federer (1969), 3.2.36, p. 272:
    uniformly close projected volumes have
    close actual probability integrals. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  SummableRealFunctionUP SummableRealArithmetic ProbabilityConstantIntegral MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureIntegralUP MeasureIntegralComparison MeasureIntegralGraphEquivalence
  PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [probability_uniform_integral_error]:
    supporting continuity of the actual intrinsic
    volume averages in Federer 3.2.36,
    p. 272. A uniform bound on the
    difference of two finite real integrands
    bounds the difference of their actual
    integrals on a probability space. Integral
    order, addition and the proved constant
    integral law give the result; no external
    integration or uniform-limit theorem is used. *)
Lemma probability_uniform_integral_error (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (f g:X->R) (a b e:R):
  mu setT= 1%E ->
  is_measure_integral mu (real_total_integrand f) a%:E ->
  is_measure_integral mu (real_total_integrand g) b%:E ->
  (forall x,`|f x-g x|<=e) ->`|a-b|<=e.
Proof.
move=>hProbability hF hG hBound.
have hCompare (u v:X->R) (c d:R):
    is_measure_integral mu (real_total_integrand u) c%:E ->
    is_measure_integral mu (real_total_integrand v) d%:E ->
    (forall x,u x<=v x) ->c<=d.
  move=>hu hv hUV.
  have hOrder:measure_almost_everywhere mu
      (partial_extended_le_locus (real_total_integrand u) (real_total_integrand v)).
    apply:(measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=>x _.
    exists (u x)%:E,(v x)%:E; split; first by apply/real_total_integrand_graph.
    split; first by apply/real_total_integrand_graph.
    by rewrite lee_fin; exact:hUV.
  have h:=measure_integral_monotone hm hu hv hOrder.
  by rewrite lee_fin in h.
have hConstant:is_measure_integral mu (real_total_integrand (fun _:X=>e)) e%:E.
  apply:(@measure_integral_graph_equivalent R X mu
    (partial_function_total (fun _:X=>(e%:E:extended_real_line R)))
    (real_total_integrand (fun _:X=>e)) e%:E _
    (@probability_constant_integral R X mu hm e hProbability))=>x y.
  exact:iff_sym (real_total_integrand_graph (fun _:X=>e) x y).
have hSides x:f x<=g x+e /\g x<=f x+e.
  have h:=hBound x; rewrite ler_norml in h; have /andP[hLow hHigh]:=h.
  split; lra.
have hUpper:a<=b+e.
  apply:(@hCompare f (fun x=>(g x+e)%R) a (b+e)%R hF
    (@real_total_integral_add R X mu hm g (fun _:X=>e) b e hG hConstant)).
  move=>x; exact:(hSides x).1.
have hLower:b<=a+e.
  apply:(@hCompare g (fun x=>(f x+e)%R) b (a+e)%R hG
    (@real_total_integral_add R X mu hm f (fun _:X=>e) a e hF hConstant)).
  move=>x; exact:(hSides x).2.
rewrite ler_norml; apply/andP; split; lra.
Qed.
