(** Federer (1969), 3.4.8(10), p. 332:
    the actual finite fibre cardinality is
    locally constant. Reuse the complete
    finite local branch assembly and its
    exact cardinality law. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology.
From Federer Require Import RelativeLocalInverseUP FiniteFibreEnumerationUP
  FiniteFibreEnumerationCardinality FiniteLocalInverseBranchAssembly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_fibre_cardinality_locally_constant]:
    each Y_nu is open, 3.4.8(10),
    p. 332. Near an original
    nu-point fibre the actual cardinality
    equals nu; no cardinality stability
    hypothesis is imposed. *)
Theorem finite_fibre_cardinality_locally_constant (R:realType) (X Y:metricType R)
    nu (P:X->Y) (Z:set X) (C:set Y) (y:Y) (a:'I_nu->X):
  continuous P ->nbhs y C ->compact [set x|Z x /\C (P x)] ->
  is_finite_fibre_enumeration P Z y a ->
  (forall x,Z x ->exists U V psi,is_relative_local_inverse P Z x U V psi) ->
  nbhs y [set z|#|` fset_set [set x|Z x /\P x = z]| = nu].
Proof.
move=>hP hC hCompact hEnumeration hCharts.
have [psi [_ [_ hNear]]]:=@finite_local_inverse_branch_assembly R X Y [the finType of 'I_nu]
  P Z C y a hP hC hCompact hEnumeration hCharts.
apply:filterS hNear=>z hz.
have hCard:=(@finite_fibre_enumeration_cardinality [the finType of 'I_nu]
  [the choiceType of (X:Type)] Y P Z z (fun i=>psi i z) hz).2.
by rewrite card_ord in hCard.
Qed.
