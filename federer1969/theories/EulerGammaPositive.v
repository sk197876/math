(** Federer (1969), 3.2.13, p. 250: the
    actual finite defining Gamma integral is strictly
    positive for each positive parameter. A zero
    integral would contradict positivity on a segment
    of Lebesgue mass one. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra.
From Federer Require Import EulerGammaUP EulerGammaBounds EulerGammaMeasurable EulerGammaFinite
  LebesgueScalarMeasure MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic PartialFunctionUP PartialFunctionBasic
  PartialExtendedOrderLoci MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence
  MeasureNonnegativeZero SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euler_gamma_positive_finite_integral]:
    existence of a finite positive Gamma(s), s>0,
    used in every denominator in Federer 3.2.13,
    pp. 250–251. Positivity follows from the
    proved zero-integral criterion, not from an extra
    property of a chosen Gamma witness. *)
Theorem euler_gamma_positive_finite_integral (R:realType) (s:R):
  (0<s)%R ->exists a:R,(0<a)%R /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) [set x:R|(0<x)%R]
      (real_total_integrand (euler_gamma_integrand s)) a%:E.
Proof.
move=>hs; have [a [ha hI]]:=euler_gamma_finite_integral hs.
exists a; split=>//.
rewrite lt_neqAle ha andbT; apply/eqP=>hZero.
have ha0:a= 0%R by symmetry.
pose u (x:R):extended_real_line R:=(gamma_positive_completion s x)%:E.
have hTotal:is_measure_integral (@lebesgue_scalar_measure R) (partial_function_total u) 0.
  change (is_measure_integral (@lebesgue_scalar_measure R) (partial_function_total u) (0%R)%:E).
  rewrite -ha0.
  apply:measure_integral_graph_equivalent _ hI=>x z.
  symmetry; exact:gamma_positive_completion_subset_graph.
have hp x:0<=u x.
  rewrite /u /gamma_positive_completion; case:ifP=>hx; rewrite lee_fin.
  - exact:ltW (euler_gamma_integrand_positive s hx).
  - exact:lexx.
have hpAE:measure_almost_everywhere (@lebesgue_scalar_measure R)
    (partial_extended_nonnegative_locus (partial_function_total u)).
  apply:(@measure_almost_everywhere_mono R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) setT _ _ (measure_almost_everywhere_true (lebesgue_scalar_is_measure R)))=>x _.
  exists (u x); by split.
have hNull:=nonnegative_integral_zero_almost_equal (lebesgue_scalar_is_measure R) hTotal hpAE.
have hSub:(`[(1%R:R),(2%R:R)]) `<=` ~` (partial_function_agreement (partial_function_total u)
    (partial_function_total (fun _:R=>(0:extended_real_line R)))).
  move=>x; rewrite /= in_itv /= =>/andP[hx1 hx2] [z [hz hz0]].
  have hx:(0<x)%R:=lt_le_trans ltr01 hx1.
  have huPositive:0<u x by rewrite /u /gamma_positive_completion hx lte_fin; exact:euler_gamma_integrand_positive.
  have huZero:u x= 0 by rewrite (hz:u x=z); symmetry.
  by rewrite huZero ltxx in huPositive.
have hMass:=measure_mono (lebesgue_scalar_is_measure R) hSub.
rewrite /measure_almost_equal /measure_almost_everywhere in hNull.
rewrite hNull in hMass.
rewrite lebesgue_scalar_segment in hMass; last by lra.
move:hMass; rewrite lee_fin; lra.
Qed.
