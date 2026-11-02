(** Federer (1969), 3.2.38, p. 275: scalar oscillation on
    a good core converts a pointwise Jacobian into a subset-integral bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureBasic
  MeasureAlmostUP MeasureSubsetIntegral SubsetIntegralAlmostConstantLower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_subset_integral_oscillation_lower]: supporting
    the point-value integral comparison in Federer 3.2.38, p. 275.
    On a finite-mass cell, an actual integrand bounded below by c-e
    gives c times the cell mass at most its integral plus e times
    the mass. The original partial integrand domain and an infinite
    integral are retained; no positive lower bound is imposed when
    c<=e, and no values are assigned outside the domain. *)
Lemma finite_subset_integral_oscillation_lower (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A:set X) (u:partial_function X (extended_real_line R))
    (I : \bar R) (c e t:R):
  is_measure mu ->measure_measurable mu A ->mu A=t%:E ->(0<=I)%E ->
  is_measure_subset_integral mu A u I ->
  measure_almost_everywhere_on mu A
    [set x|exists z,partial_function_graph u x z /\(c-e)%R%:E<=z]%E ->
  (c%:E*mu A<=I+(e*t)%R%:E)%E.
Proof.
move=>hm hA hMass hI0 hIntegral hLower.
have ht:0<=t by have h:=measure_nonnegative hm A; rewrite hMass lee_fin in h.
rewrite hMass -EFinM.
case:(leP c e)=>[hCe|hEc].
- have hBound:((c*t)%R%:E<=(e*t)%R%:E)%E.
    rewrite lee_fin; exact (ler_wpM2r ht hCe).
  apply:le_trans hBound _.
  have h:=leeD hI0 (lexx ((e*t)%:E)); by rewrite add0e in h.
- have hPositive:0<c-e by rewrite subr_gt0.
  have hBound:=@subset_integral_almost_positive_constant_lower R X mu A u I (c-e)
    hm hA hPositive hIntegral hLower.
  rewrite hMass -EFinM in hBound.
  have hSum:=leeD hBound (lexx ((e*t)%:E)).
  have hIdentity:((c-e)*t+e*t)=c*t by ring.
  by rewrite -EFinD hIdentity in hSum.
Qed.
