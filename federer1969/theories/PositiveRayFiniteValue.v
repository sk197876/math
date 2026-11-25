(** Federer (1969), 3.2.13, p. 250: a summable outer
    polar integrand has a finite value at a positive radius.
    This uses the almost-finiteness consequence of 2.4.3(4), p. 82. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostUP
  MeasureSummableFiniteValues MeasureIntegralUP LebesgueScalarMeasure ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_ray_summable_finite_value]: supporting
    selection of a finite positive-radius fibre from a finite
    polar integral in Federer 3.2.13, p. 250. Only an
    existence conclusion is exposed; no radius is globally selected. *)
Lemma positive_ray_summable_finite_value (R:realType)
    (f:partial_function R (extended_real_line R)):
  is_measure_summable (@lebesgue_scalar_measure R) f ->
  exists r v,(0<r)%R /\partial_function_graph f r v /\v\is a fin_num.
Proof.
move=>hI.
have hAE:=measure_summable_finite_almost (lebesgue_scalar_is_measure R) hI.
apply:contrapT=>hNone.
have hSub:`[(1%R:R),(2%R:R)] `<=` ~`(partial_extended_finite_locus f).
  move=>x; rewrite /= in_itv /= =>/andP[hx1 hx2] [v [hv hFin]].
  apply:hNone; exists x,v; split; first exact:lt_le_trans ltr01 hx1.
  by split.
have hMass:=measure_mono (lebesgue_scalar_is_measure R) hSub.
rewrite /measure_almost_everywhere in hAE; rewrite hAE lebesgue_scalar_segment in hMass; last by lra.
move:hMass; rewrite lee_fin; lra.
Qed.
