(** Federer (1969), 2.3.2(5), p. 73, and numerical operations on p. 74:
    measurability of the pair on the common domain. We use countable
    coordinate bases and the product-neighborhood definition. *)
From mathcomp Require Import all_boot classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPair PartialFunctionPreimages
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure MeasureCountableClosure
  MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [indexed_base_refines_neighborhood]: supporting
    neighborhood form of the coordinate-base property used in
    Federer 2.3.2(5), p. 73. No enumeration of a
    distinguished empty member is needed for this formulation. *)
Lemma indexed_base_refines_neighborhood (Y : topologicalType) (J : Type)
    (U : J -> set Y) :
  (forall V, open V -> forall y, V y -> exists j, U j y /\ U j `<=` V) ->
  forall y V, nbhs y V -> exists j, U j y /\ U j `<=` V.
Proof.
move=> hr y V; rewrite nbhsE=> -[W [ho hy] hWV].
have [j [hj hjW]] := hr W ho y hy; exists j; split=> //.
exact: subset_trans hjW hWV.
Qed.

(** Source for [measurable_partial_function_pair]: supporting
    binary case of Federer 2.3.2(5), p. 73, applied to
    the numerical operations on p. 74. Countable factor bases
    are supplied as arbitrary countable-type indexed families;
    the paired map is defined precisely on the common domain. *)
Theorem measurable_partial_function_pair (R : realType) (X : choiceType)
    (Y Z : topologicalType) (J K : countType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) (g : partial_function X Z)
    (U : J -> set Y) (V : K -> set Z) :
  (forall j, open (U j)) ->
  (forall O, open O -> forall y, O y -> exists j, U j y /\ U j `<=` O) ->
  (forall k, open (V k)) ->
  (forall O, open O -> forall z, O z -> exists k, V k z /\ V k `<=` O) ->
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_function_pair f g).
Proof.
move=> hU hrU hV hrV hf hg; constructor.
- rewrite partial_function_pair_domain.
  exact: (@measure_almost_everywhere_and R X mu hm _ _
    (measurable_function_domain hf) (measurable_function_domain hg)).
- move=> O ho.
  pose D := [set p : J * K | U p.1 `*` V p.2 `<=` O].
  have he : O = \bigcup_(p in D) (U p.1 `*` V p.2).
    apply/seteqP; split=> [[y z] hx|x [p hp hx]]; last exact: hp hx.
    have hn : nbhs (y,z) O by rewrite openE in ho; exact: ho _ hx.
    have [[A B] [hA hB] hAB] := hn.
    have [j [hjy hjA]] := @indexed_base_refines_neighborhood Y J U hrU y A hA.
    have [k [hkz hkB]] := @indexed_base_refines_neighborhood Z K V hrV z B hB.
    exists (j,k); last by split.
    move=> [a b] [ha hb]; apply: hAB; split; [exact: hjA _ ha|exact: hkB _ hb].
  rewrite he partial_function_preimage_union.
  apply: (@measure_measurable_countable_union R X _ mu hm _ _ (countableP _))=> p hp.
  case: p hp=> j k hjk.
  rewrite partial_function_pair_rectangle_preimage.
  exact (@measure_measurable_intersection R X mu hm _ _
    (@measurable_function_open_preimage R X Y mu f hf (U j) (hU j))
    (@measurable_function_open_preimage R X Z mu g hg (V k) (hV k))).
Qed.
