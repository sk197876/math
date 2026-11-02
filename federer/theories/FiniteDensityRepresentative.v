(** Federer (1969), 3.2.20, p. 257: supporting nonnegative
    finite representatives of the measurable Jacobians in the two
    applications of 3.2.5(2). The public Jacobian keeps its partial domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasurableTotalExtension
  MeasurableFiniteRealParts MeasurableRealEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonnegative_finite_density_representative]: supporting
    auxiliary representative in Federer 3.2.20, p. 257,
    justified by the null-modification convention of 2.3.2, p. 73.
    Existence uses existing opaque extension laws. The representative
    agrees at every actual graph point and is nonnegative everywhere;
    no globally selected function is introduced here. *)
Lemma nonnegative_finite_density_representative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (d : partial_function X (real_line_metric R)) :
  is_measure_measurable_function mu d ->
  (forall x j,partial_function_graph d x j -> 0<=j) ->
  exists p : X -> R,
    (forall x,0<=p x) /\
    is_measure_measurable_function mu
      (partial_function_total (fun x=>(p x)%:E : extended_real_line R)) /\
    is_partial_function_total_extension d p /\
    measure_almost_equal mu d (partial_function_total p).
Proof.
move=> hd hPos.
have [F [hExt [hAE hF]]] := measurable_function_total_extension hm (0:real_line_metric R) hd.
pose p (x : X) : real_line_metric R := Num.max (F x) 0.
have hp0 x : 0<=p x by rewrite /p le_max lexx orbT.
have hpMeas := (measurable_finite_real_parts hm hF).1.
have hpExt : is_partial_function_total_extension d p.
  move=> x j hj; rewrite /p (hExt x j hj); exact: (max_idPl (hPos x j hj)).
exists p; split; first exact hp0.
split; first exact: (measurable_total_real_embedding hm hpMeas).
split; first exact hpExt.
exact: (partial_function_total_extension_almost_equal (measurable_function_domain hd) hpExt).
Qed.
