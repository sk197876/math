(** Federer (1969), 3.2.22(3), p. 260:
    the signed part reduction for actual fibre integrals,
    using 2.4.4(6), p. 82. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition PartialZeroExtension PartialZeroExtensionLaws PartialFunctionIntegralParts
  MeasureUpperIntegralPositivePart MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  ParameterizedIntegral ParameterizedIntegralLaws ParameterizedIntegralParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [parameterized_subset_total_postcomposition]:
    supporting positive and negative fibre parts in
    Federer 3.2.22(3), p. 260. A scalar map
    fixing zero commutes with the subset cutoff, so
    the two inner-integrand families have exactly the
    same actual parameterized-integral graphs. *)
Lemma parameterized_subset_total_postcomposition (R:realType) (X Y:choiceType)
    (beta:set X->\bar R) (C:Y->set X) (u:X->extended_real_line R)
    (phi:extended_real_line R->extended_real_line R):
  phi 0=0 ->forall y a,
    partial_function_graph (parameterized_integral beta (fun y=>partial_function_zero_extension
      (0:extended_real_line R) (C y) (partial_function_total (fun x=>phi (u x))))) y a <->
    partial_function_graph (parameterized_integral beta (fun y=>partial_function_postcompose
      (partial_function_zero_extension (0:extended_real_line R) (C y) (partial_function_total u)) phi)) y a.
Proof.
move=>hZero; apply:parameterized_integral_graph_equivalent=>y x z.
rewrite (partial_zero_extension_postcompose (C y) (partial_function_total u) x z hZero).
rewrite !partial_function_zero_extension_graph.
split.
- move=>[[hx hz]|[hx hz]]; last by right; split.
  left; split; first exact hx; exists (u x); by split.
- move=>[[hx [t [ht hz]]]|[hx hz]]; last by right; split.
  left; split; first exact hx.
  change (phi (u x)=z); by rewrite (ht:u x=t).
Qed.

(** Source for [parameterized_subset_total_integral_from_parts]:
    the signed standard approximation in Federer 3.2.22,
    p. 260. A defined difference of the two outer
    nonnegative part integrals gives the actual signed
    iterated integral. Undefined differences of infinities
    remain undefined on every individual fibre. *)
Theorem parameterized_subset_total_integral_from_parts (R:realType) (X Y:choiceType)
    (alpha:set Y->\bar R) (beta:set X->\bar R) (ha:is_measure alpha) (hb:is_measure beta)
    (C:Y->set X) (u:X->extended_real_line R) P N a:
  is_measure_integral alpha (parameterized_integral beta (fun y=>partial_function_zero_extension
    (0:extended_real_line R) (C y) (partial_function_total (fun x=>extended_positive_part (u x))))) P ->
  is_measure_integral alpha (parameterized_integral beta (fun y=>partial_function_zero_extension
    (0:extended_real_line R) (C y) (partial_function_total (fun x=>extended_negative_part (u x))))) N ->
  extended_subtract P N=Some a ->
  is_measure_integral alpha (parameterized_integral beta (fun y=>partial_function_zero_extension
    (0:extended_real_line R) (C y) (partial_function_total u))) a.
Proof.
move=>hP hN hDifference.
have hPZero:(@extended_positive_part R 0)=0 by rewrite /extended_positive_part maxxx.
have hNZero:(@extended_negative_part R 0)=0 by rewrite /extended_negative_part oppe0 /extended_positive_part maxxx.
have hPGraph:=@parameterized_subset_total_postcomposition R X Y beta C u (@extended_positive_part R) hPZero.
have hNGraph:=@parameterized_subset_total_postcomposition R X Y beta C u (@extended_negative_part R) hNZero.
exact:(parameterized_integral_from_parts ha hb
  (measure_integral_graph_equivalent hPGraph hP) (measure_integral_graph_equivalent hNGraph hN) hDifference).
Qed.
