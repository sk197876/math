(** Federer (1969), 3.2.7, p. 246: supporting
    finiteness of the target integral of a summable
    weight, for either order of the endpoint values.
    Use measurable restrictions and finite subtraction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype ring.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence LebesgueScalarMeasure EuclideanLebesgueBoxes
  SummableRealFunctionUP SummableRealArithmetic SummableSubsetRestriction EndpointLevelSigns ScalarSignedMultiplicityAlmost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_open_interval_cutoff_graph]:
    supporting exact restriction of the target weight
    in Federer 3.2.7, p. 246. Open interval
    indicators retain a finite value at every point. *)
Lemma real_open_interval_cutoff_graph (R:realType) (g:R->R) (a b:R) x z:
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
    (`]a,b[:set (real_line_metric R)) (real_total_integrand g)) x z <->
  partial_function_graph (real_total_integrand (fun y=>g y*((a<y)&&(y<b))%:R)) x z.
Proof.
rewrite real_total_integrand_graph.
case:(boolP ((a<x)&&(x<b)))=>hRange.
- have hx:(`]a,b[:set (real_line_metric R)) x by rewrite /= in_itv.
  rewrite (partial_function_zero_extension_on _ _ _ hx) real_total_integrand_graph ?hRange /= mulr1.
  exact:iff_refl.
- have hx:~(`]a,b[:set (real_line_metric R)) x by rewrite /= in_itv; exact/negP.
  rewrite (partial_function_zero_extension_off _ _ _ hx) ?(negbTE hRange) /= mulr0.
  split; exact:Logic.eq_sym.
Qed.

(** Source for [summable_oriented_indicator]:
    finite target integral in the third example
    of Federer 3.2.7, p. 246. Every
    globally summable g remains summable after
    multiplication by the oriented endpoint indicator. *)
Theorem summable_oriented_indicator (R:realType) (g:R->R) (a b:R):
  is_measure_summable (@lebesgue_scalar_measure R) (real_total_integrand g) ->
  is_measure_summable (@lebesgue_scalar_measure R) (scalar_oriented_interval_integrand g a b).
Proof.
move=>hg; have hm:=lebesgue_scalar_is_measure R.
have [p hp]:=summable_measurable_zero_extension hm
  (lebesgue_scalar_open_interval_measurable a b) hg.
have [q hq]:=summable_measurable_zero_extension hm
  (lebesgue_scalar_open_interval_measurable b a) hg.
have hP:=measure_integral_graph_equivalent (real_open_interval_cutoff_graph g a b) hp.
have hQ:=measure_integral_graph_equivalent (real_open_interval_cutoff_graph g b a) hq.
have hD:=real_total_integral_subtract hm hP hQ.
exists (p-q).
apply:(measure_integral_graph_equivalent _ hD)=>x z.
rewrite real_total_integrand_graph.
change ((g x*((a<x)&&(x<b))%:R-g x*((b<x)&&(x<a))%:R)%:E=z <->
  (g x*oriented_level_indicator a b x)%:E=z).
by rewrite /oriented_level_indicator mulrBr.
Qed.
