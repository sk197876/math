(** Federer (1969), 4.1.18, p. 375: each field in
    Omega_m is summable, and its L1 size is the literal
    mass integral used in J. Reuse 2.4.12 and 2.4.16,
    including the original countable-measurability clause. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP
  PartialFunctionBasic PartialNormPower RealPower
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureLpNorm
  MeasureLpMembershipUP MeasureLpCountableMeasurability
  MeasureLoneNormIntegralGeneral SummableRealFunctionUP
  CompactSummableFieldSealed CompactSummableFieldLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section Integral.
Variable R:realType.
Variable X:topologicalType.
Variable V:lmodType R.
Variable N:V->R.
Variable hN:is_real_norm N.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Local Notation W:=(@CompactSummableField.space R X V N hN mu hm).
Local Notation value:=(@compact_summable_field_value R X V N hN mu hm).
Local Notation size:=(@compact_summable_field_size R X V N hN mu hm).

(** Source for [compact_summable_field_lone]: full L1
    membership of the actual fields in Omega_m, Federer
    4.1.18, p. 375. Countable measurability follows from
    finite L1 size by the parenthesis in 2.4.12, p. 86. *)
Theorem compact_summable_field_lone (f:W):
  @is_measure_lp_function R X V N hN mu 1
    (partial_function_total (value f)).
Proof.
have hMeas:=@compact_summable_field_measurable R X V N hN mu hm f.
have hFinite:=@compact_summable_field_finite R X V N hN mu hm f.
split;first exact:lexx.
split;first exact:hMeas.
split;first exact:hFinite.
exact:(@finite_lp_norm_countably_measurable R X V N hN mu hm 1
  (partial_function_total (value f)) (lexx 1) hMeas.1 hFinite).
Qed.

(** Source for [compact_summable_field_size_integral]: the
    original integral of the multivector mass in the J
    formula of Federer 4.1.18, p. 375. The norm and
    integral are the previously specified actual objects. *)
Theorem compact_summable_field_size_integral (f:W):
  is_measure_integral mu (real_total_integrand (fun x=>N (value f x)))
    (size f)%:E.
Proof.
have hMeas:=@compact_summable_field_measurable R X V N hN mu hm f.
have hIntegral:=@measurable_lone_norm_integral R X V N hN mu hm
  (partial_function_total (value f)) hMeas.1.
have hSize:measure_lp_norm mu N 1 (partial_function_total (value f))=(size f)%:E.
  exact:esym (@compact_summable_field_size_exact R X V N hN mu hm f).
rewrite hSize in hIntegral.
apply:(@measure_integral_graph_equivalent R X mu _ _ (size f)%:E _ hIntegral).
move=>x y;split.
- move=>[v [hV hY]];apply/real_total_integrand_graph.
  have hValue:value f x=v:=hV.
  rewrite -hValue in hY.
  by rewrite (real_power_one_exponent (real_seminorm_nonnegative hN.1 _)) in hY.
- move/real_total_integrand_graph=>hY.
  exists (value f x);split;first by [].
  by rewrite (real_power_one_exponent (real_seminorm_nonnegative hN.1 _)).
Qed.
End Integral.
