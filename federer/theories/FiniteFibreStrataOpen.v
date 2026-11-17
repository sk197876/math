(** Federer (1969), 3.4.8(10), p. 332:
    the sets Y_nu of actual fibre
    cardinality nu are open. Apply
    the proved local cardinality theorem;
    the ordered sequence size equals the actual finite cardinal. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology.
From Federer Require Import RelativeLocalInverseUP FiniteFibreEnumerationUP FiniteOrderedEnumeration
  OrderedFibreSequences FiniteFibreEnumerationCardinality FiniteFibreCardinalityLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_fibre_strata_open]:
    the original sets Y_0,...,Y_k
    are open and disjoint, 3.4.8(10),
    p. 332. Here the actual
    finite fibre cardinal is used directly;
    the ordering only supplies its initial enumeration. *)
Theorem finite_fibre_strata_open (R:realType) (X Y:metricType R)
    (P:X->Y) (Z:set X) (V:set Y) (xi:X->R) (S:Y->seq X) (x0:X):
  continuous P ->open V ->
  (forall y,V y ->is_finite_ordered_enumeration [set x|Z x /\P x = y] xi (S y)) ->
  (forall y,V y ->exists C:set Y,nbhs y C /\compact [set x|Z x /\C (P x)]) ->
  (forall x,Z x ->exists U W psi,is_relative_local_inverse P Z x U W psi) ->
  forall nu,open [set y|V y /\#|` fset_set [set x|Z x /\P x = y]| = nu].
Proof.
move=>hP hOpen hS hCompact hCharts nu;rewrite openE=>y [hy hCard].
have hEnumeration:=@ordered_sequence_fibre_enumeration R [the choiceType of (X:Type)] Y
  P Z y xi x0 (S y) (hS y hy).
have hSize:=(@finite_fibre_enumeration_cardinality [the finType of 'I_(size (S y))]
  [the choiceType of (X:Type)] Y P Z y (fun i=>nth x0 (S y) (i:nat)) hEnumeration).2.
rewrite card_ord in hSize.
have [C [hC hK]]:=hCompact y hy.
have hNear:=@finite_fibre_cardinality_locally_constant R X Y (size (S y)) P Z C y
  (fun i=>nth x0 (S y) (i:nat)) hP hC hK hEnumeration hCharts.
have hV:nbhs y V by rewrite openE in hOpen;exact:hOpen y hy.
apply:filterS (filterI hV hNear)=>z [hzV hzCard];split;first exact:hzV.
by rewrite hzCard -hSize.
Qed.
