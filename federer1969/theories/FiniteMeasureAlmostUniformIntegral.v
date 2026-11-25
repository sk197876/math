(** Federer (1969), 4.1.14, p. 371: passing to the limit in
    the weighted image estimates. This supporting consequence of
    2.4.4(7)–(8), pp. 82–83, permits a uniform error only on
    a conull part of a finite measure space. It therefore applies
    to the actual variation, which is carried by the original
    compact support. The measure and its total mass may be zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal lra.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialAbsolutePartsGraph PartialExtendedOrderLoci SummableRealFunctionUP
  SummableRealArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralAbsolute MeasureIntegralComparison
  MeasureIntegralGraphEquivalence FiniteMeasureBoundedNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_measure_almost_uniform_integral_error]:
    the actual scalar integral error is at most the uniform
    conull error times the original finite mass, supporting
    Federer 4.1.14, p. 371, by 2.4.4(7), p. 82. *)
Theorem finite_measure_almost_uniform_integral_error
    (R:realType) (X:choiceType) (mu:set X->\bar R)
    (hm:is_measure mu) (mass:R) (f g:X->R) (a b e:R):
  mu setT=mass%:E->
  is_measure_integral mu (real_total_integrand f) a%:E->
  is_measure_integral mu (real_total_integrand g) b%:E->
  measure_almost_everywhere mu [set x | `|f x-g x|<=e]->
  `|a-b|<=e*mass.
Proof.
move=>hMass hF hG hError.
have hDifference:=@real_total_integral_subtract R X mu hm f g a b hF hG.
have [c [hAbsolute hLower]]:=@measure_integral_absolute_bound R X mu hm
  (real_total_integrand (fun x=>f x-g x)) (a-b)%:E hDifference.
have hConstant:is_measure_integral mu
    (real_total_integrand (fun _:X=>e)) (e*mass)%:E.
  have hRaw:=@finite_measure_constant_integral R X mu hm mass e hMass.
  apply:(@measure_integral_graph_equivalent R X mu _ _ _ _ hRaw)=>x y.
  exact:iff_sym (real_total_integrand_graph (fun _:X=>e) x y).
have hOrder:measure_almost_everywhere mu
    (partial_extended_le_locus
      (partial_extended_function_absolute_value
        (real_total_integrand (fun x=>f x-g x)))
      (real_total_integrand (fun _:X=>e))).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hError)=>x hx.
  exists (`|f x-g x|)%:E,e%:E;split.
  - exists (f x-g x)%:E;split;first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split;first by apply/real_total_integrand_graph.
    by rewrite lee_fin.
have hUpper:=@measure_integral_monotone R X mu hm _ _ c
  (e*mass)%:E hAbsolute hConstant hOrder.
have h:=le_trans hLower hUpper.
by rewrite abse_EFin lee_fin in h.
Qed.

(** Source for [finite_measure_almost_uniform_integral_limit]:
    uniformly converging weights on a conull part of the
    original finite variation have converging actual integrals,
    supporting Federer 4.1.14, p. 371. Integral values and
    their domains are not replaced by a new integration theory. *)
Theorem finite_measure_almost_uniform_integral_limit
    (R:realType) (X:choiceType) (mu:set X->\bar R)
    (hm:is_measure mu) (mass:R) (f:nat->X->R) (g:X->R)
    (a:nat->R) (b:R):
  mu setT=mass%:E->
  (forall i,is_measure_integral mu (real_total_integrand (f i)) (a i)%:E)->
  is_measure_integral mu (real_total_integrand g) b%:E->
  (forall delta:R,0<delta->exists N:nat,forall i:nat,(N<=i)%N->
    measure_almost_everywhere mu [set x | `|f i x-g x|<=delta])->
  forall eps:R,0<eps->exists N:nat,forall i:nat,(N<=i)%N->`|a i-b|<eps.
Proof.
move=>hMass hF hG hUniform eps hEps.
have hMass0:0<=mass.
  have h:=measure_nonnegative hm setT;by rewrite hMass lee_fin in h.
have hDen:0<mass+1 by lra.
have hDelta:0<eps/(mass+1) by rewrite divr_gt0.
have [N hN]:=hUniform _ hDelta.
exists N=>i hi.
have hBound:=@finite_measure_almost_uniform_integral_error R X mu hm
  mass (f i) g (a i) b (eps/(mass+1)) hMass (hF i) hG (hN i hi).
apply:(le_lt_trans hBound).
have hCancel:eps/(mass+1)*(mass+1)=eps by rewrite divfK // gt_eqF.
have hPositive:0<eps/(mass+1):=hDelta.
nra.
Qed.
