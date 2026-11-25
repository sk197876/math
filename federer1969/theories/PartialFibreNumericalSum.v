(** Federer (1969), 3.2.3(2), p. 243: public exact
    partial fibre sum. Only the opaque graph specification
    is used; undefined input values and undefined signed
    sums stay outside the domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFibreNumericalSumUP
  PartialFibreNumericalSumSealed PartialFunctionExtensionUP NumericalSum NumericalSumValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_fibre_numerical_sum]: the inner
    integral's sum in Federer 3.2.3(2), p. 243,
    accessed through its opaque graph laws. *)
Definition partial_fibre_numerical_sum (R:realType) (X:choiceType) (Y:Type)
    (p:X->Y) (u:partial_function X (extended_real_line R)):=
  PartialFibreNumericalSum.value p u.

(** Source for [partial_fibre_numerical_sum_graph]: exact
    graph and domain of the fibre sum in Federer
    3.2.3(2), p. 243, using 2.1.1(4), p. 52. *)
Lemma partial_fibre_numerical_sum_graph (R:realType) (X:choiceType) (Y:Type)
    (p:X->Y) (u:partial_function X (extended_real_line R)) y z:
  partial_function_graph (partial_fibre_numerical_sum p u) y z <-> exists w:X->\bar R,
    (forall x,p x=y -> partial_function_graph u x (w x)) /\
    numerical_sum [set x|p x=y] w=Some z.
Proof. exact:PartialFibreNumericalSum.laws. Qed.

(** Source for [partial_fibre_numerical_sum_extension_graph]:
    null-extension step in Federer 3.2.3(2), p. 243,
    using 2.3.2, p. 73. A total representative changes
    the fibre graph only on images of the original
    undefined set; no representative is part of the definition. *)
Lemma partial_fibre_numerical_sum_extension_graph (R:realType) (X:choiceType) (Y:Type)
    (p:X->Y) (u:partial_function X (extended_real_line R)) (U:X->extended_real_line R) y z:
  is_partial_function_total_extension u U ->
  (forall x,p x=y -> partial_function_domain u x) ->
  (partial_function_graph (partial_fibre_numerical_sum p u) y z <->
    numerical_sum [set x|p x=y] U=Some z).
Proof.
move=>hExt hDom; rewrite partial_fibre_numerical_sum_graph; split.
- move=>[w [hw hSum]].
  have he:numerical_sum [set x|p x=y] w=numerical_sum [set x|p x=y] U.
    apply:numerical_sum_ext=>x hx; symmetry; exact (hExt x (w x) (hw x hx)).
  by rewrite -he.
- move=>hSum; exists U; split=>//; move=>x hx.
  have [a ha]:=hDom x hx; by rewrite (hExt x a ha).
Qed.
