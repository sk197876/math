(** Federer (1969), 3.2.22(3), p. 258:
    the iterated integral may be restricted to Z,
    since every original fibre outside Z is empty. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  PartialMappingMultiplicity MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureDensityNullSets ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_fibre_integral_off_image_zero]:
    supporting outer-domain restriction in Federer
    3.2.22(3), p. 258. Outside Z the actual
    fibre is empty, so its integral exists and is
    exactly zero for any partial weight. This proves
    a value instead of defaulting a nonintegrable fibre. *)
Lemma partial_fibre_integral_off_image_zero (R:realType) (X:choiceType) (Y:Type)
    (beta:set X->\bar R) (hb:is_measure beta) (f:partial_function X Y)
    (g:partial_function X (extended_real_line R)) (Z:set Y):
  (forall x y,partial_function_graph f x y ->Z y) ->forall y a,~Z y ->
  (partial_function_graph (parameterized_integral beta (fun y=>partial_function_zero_extension
    (0:extended_real_line R) (partial_mapping_fibre f y) g)) y a <->a=0).
Proof.
move=>hImage y a hNot.
have hEmpty:partial_mapping_fibre f y=set0.
  apply/seteqP; split=>[x hx|x []]; exact:(hNot (hImage x y hx)).
pose section:=partial_function_zero_extension (0:extended_real_line R) (partial_mapping_fibre f y) g.
have hGraph x z:partial_function_graph section x z <->partial_function_graph
    (partial_function_total (fun _ : X=>(0:extended_real_line R))) x z.
  rewrite /section hEmpty (partial_function_zero_extension_off _ _ _ (fun h:set0 x=>h)).
  change (z=0 <->0=z); split=>h; exact:esym h.
have hZero:is_measure_integral beta section 0.
  exact:(measure_integral_graph_equivalent (fun x z=>iff_sym (hGraph x z)) (measure_extended_zero_integral hb)).
rewrite parameterized_integral_specification; split.
- move=>hI; exact:(measure_integral_unique hI hZero).
- by move=>->.
Qed.

(** Source for [partial_fibre_integral_target_cutoff_graph]:
    the outer integral over Z in Federer 3.2.22(3),
    p. 258. The actual inner-integral graph is
    already zero off Z, so its Z cutoff has
    exactly the same graph, not just the same integral.
    No measurability assumption on an arbitrary extension
    of the inner integral is introduced. *)
Lemma partial_fibre_integral_target_cutoff_graph (R:realType) (X:choiceType) (Y:Type)
    (beta:set X->\bar R) (hb:is_measure beta) (f:partial_function X Y)
    (g:partial_function X (extended_real_line R)) (Z:set Y):
  (forall x y,partial_function_graph f x y ->Z y) ->
  let h:=parameterized_integral beta (fun y=>partial_function_zero_extension
    (0:extended_real_line R) (partial_mapping_fibre f y) g) in
  forall y a,partial_function_graph (partial_function_zero_extension (0:extended_real_line R) Z h) y a <->
    partial_function_graph h y a.
Proof.
move=>hImage h y a; have [hy|hy]:=pselect (Z y).
- exact:(partial_function_zero_extension_on _ _ _ hy).
- rewrite (partial_function_zero_extension_off _ _ _ hy).
  symmetry; exact:(@partial_fibre_integral_off_image_zero R X Y beta hb f g Z hImage y a hy).
Qed.
