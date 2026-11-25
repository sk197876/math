(** Federer (1969), 3.2.22, pp. 259–260:
    exact support bookkeeping for local source and target
    integrals, using 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [subset_integral_total_agreement]: supporting
    exact local representative changes in Federer 3.2.22,
    pp. 259–260. Agreement on A suffices to
    preserve its actual subset integral, independently
    of values outside A or definedness of a signed integral. *)
Lemma subset_integral_total_agreement (R:realType) (X:choiceType)
    (rho:set X->\bar R) (A:set X) (u v:X->extended_real_line R) a:
  (forall x,A x ->u x=v x) ->
  is_measure_subset_integral rho A (partial_function_total u) a <->
  is_measure_subset_integral rho A (partial_function_total v) a.
Proof.
move=>hAgree.
have hGraph x z:partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
      A (partial_function_total u)) x z <->
    partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
      A (partial_function_total v)) x z.
  have [hx|hx]:=pselect (A x).
  - rewrite !(partial_function_zero_extension_on _ _ _ hx).
    change (u x=z <->v x=z); by rewrite (hAgree x hx).
  - by rewrite !(partial_function_zero_extension_off _ _ _ hx).
split; [exact:measure_integral_graph_equivalent hGraph|exact:measure_integral_graph_equivalent (fun x z=>iff_sym (hGraph x z))].
Qed.

(** Source for [subset_integral_total_supported]: supporting
    the C_j and gamma_j(C_j) cutoffs in Federer
    3.2.22, p. 260. A total function zero
    outside A has precisely the same integral and
    subset integral, including zero times infinity. *)
Lemma subset_integral_total_supported (R:realType) (X:choiceType)
    (rho:set X->\bar R) (A:set X) (u:X->extended_real_line R) a:
  (forall x,~A x ->u x=0%E) ->
  is_measure_subset_integral rho A (partial_function_total u) a <->
  is_measure_integral rho (partial_function_total u) a.
Proof.
move=>hOff.
have hGraph x z:partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
      A (partial_function_total u)) x z <->u x=z.
  have [hx|hx]:=pselect (A x).
  - exact:(partial_function_zero_extension_on _ _ _ hx).
  - rewrite (partial_function_zero_extension_off _ _ _ hx) (hOff x hx).
    split=>h; exact:esym h.
split=>hI.
- apply:(measure_integral_graph_equivalent _ hI)=>x z; exact:(hGraph x z).
- apply:(measure_integral_graph_equivalent _ hI)=>x z; exact:iff_sym (hGraph x z).
Qed.
