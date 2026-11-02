(** Federer (1969), 3.2.20, p. 257: the displayed
    equality of the two fibre counts under each univalent compact
    chart, and the unit multiplicity of the chart itself. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MappingMultiplicity MappingMultiplicityLaws CountingMeasure CountingInjectionBound
  CountingImageBound ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_multiplicity_injective_chart]: the equality
    N(f restricted to psi(K),z)=N((f composed with psi) restricted
    to K,z) in Federer 3.2.20, p. 257. Only injectivity
    on K is needed; fibres may be infinite. *)
Lemma mapping_multiplicity_injective_chart (R : realType) (X Y Z : choiceType)
    (K : set X) (psi : X -> Y) (F : Y -> Z) z :
  (forall x y,K x -> K y -> psi x=psi y -> x=y) ->
  @mapping_multiplicity R X Z (fun x=>F (psi x)) K z=
    @mapping_multiplicity R Y Z F (psi @` K) z.
Proof.
move=> hInj.
have hFibre : mapping_fibre F (psi @` K) z=
    psi @` mapping_fibre (fun x=>F (psi x)) K z.
  apply/seteqP; split=> y.
  - move=> [[x hx hVal] hF]; exists x; last exact hVal.
    split; first exact hx; by rewrite hVal.
  - move=> [x [hx hF] hVal]; split; first by exists x.
    by rewrite -hVal.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@counting_measure_injection_bound R X Y _ _ psi).
  + move=> x [hx hF]; split; first by exists x.
    exact hF.
  + move=> x y hx hy hEq; exact: (hInj x y hx.1 hy.1 hEq).
- rewrite /mapping_multiplicity hFibre; exact: counting_measure_image_bound.
Qed.

(** Source for [mapping_multiplicity_univalent_image]: unit multiplicity
    of psi restricted to K on its image in the second transformation
    of Federer 3.2.20, p. 257. It holds pointwise, without
    any measurability or finite-cardinality assumption on K. *)
Lemma mapping_multiplicity_univalent_image (R : realType) (X Y : choiceType)
    (K : set X) (psi : X -> Y) y :
  (forall x z,K x -> K z -> psi x=psi z -> x=z) ->
  (psi @` K) y -> @mapping_multiplicity R X Y psi K y= 1.
Proof.
move=> hInj [x hx hVal].
have hFibre : mapping_fibre psi K y=[set x].
  apply/seteqP; split=> z.
  - move=> [hz hZVal]; exact: (hInj z x hz hx (eq_trans hZVal (esym hVal))).
  - move=> ->; by split.
by rewrite /mapping_multiplicity hFibre counting_measure_singleton_value.
Qed.

(** Source for [univalent_multiplicity_weight_graph]: the target
    integral over psi(K) in the second application of 3.2.5(2),
    Federer 3.2.20, p. 257. Arbitrary extended-real
    weights retain exact graph equality with subset zero extension. *)
Lemma univalent_multiplicity_weight_graph (R : realType) (X Y : choiceType)
    (K : set X) (psi : X -> Y) (g : Y -> \bar R) :
  (forall x z,K x -> K z -> psi x=psi z -> x=z) -> forall y a,
  partial_function_graph (partial_function_total
    (fun y=>g y* @mapping_multiplicity R X Y psi K y : extended_real_line R)) y a <->
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) (psi @` K)
    (partial_function_total (fun y=>g y : extended_real_line R))) y a.
Proof.
move=> hInj y a; change (g y* @mapping_multiplicity R X Y psi K y=a <->
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R) (psi @` K)
    (partial_function_total (fun y=>g y : extended_real_line R))) y a).
case: (pselect ((psi @` K) y))=> hy.
- rewrite (@mapping_multiplicity_univalent_image R X Y K psi y hInj hy) mule1
    (partial_function_zero_extension_on _ _ _ hy); reflexivity.
- rewrite ((@mapping_multiplicity_zero_iff R X Y psi K y).2 hy) mule0
    (partial_function_zero_extension_off _ _ _ hy).
  split=> h; exact: (esym h).
Qed.
