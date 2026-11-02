(** Federer (1969), 3.2.3, p. 243: null
    source changes and discarded critical points do not
    change either side of the area formula when both
    the Jacobian mass and image measure of the excess vanish. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasureNullModification
  MeasureIntegralUP MeasureIntegralAlmostEquality MappingMultiplicity MappingMultiplicityLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_formula_null_image_modification]: the
    null and Borel reductions in Federer 3.2.3,
    p. 243. Counting fibres agree outside the image
    of the excess; exact integral and partial-domain
    null-invariance then transfer the formula. *)
Theorem area_formula_null_image_modification (R:realType) (X Y:choiceType)
    (f:X->Y) (nu:set X->\bar R) (beta:set Y->\bar R)
    (hn:is_measure nu) (hb:is_measure beta) (C A:set X):
  C `<=` A -> nu (A `\` C)=0 -> beta (f @` (A `\` C))=0 ->
  is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f C y:extended_real_line R))) (nu C) ->
  is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f A y:extended_real_line R))) (nu A).
Proof.
move=>hCA hN hImage hInt.
have hValue:nu C=nu A.
  apply:(@measure_null_modification_value R X nu hn C A (A `\` C) hN)=>x hx.
  split; first exact (hCA x).
  move=>ha; apply:contrapT=>hc; exact (hx (conj ha hc)).
rewrite -hValue.
apply:(@measure_integral_almost_equal R Y beta hb _ _ _ hInt).
have hAE:measure_almost_everywhere beta (~` (f @` (A `\` C))).
  by rewrite /measure_almost_everywhere setCK.
apply:(@measure_almost_everywhere_mono R Y beta hb _ _ _ hAE)=>y hy.
have hEq:=@mapping_fibre_sandwich_equal X Y f C A A y hCA (fun x hx=>hx) hy.
exists (@mapping_multiplicity R X Y f C y); split; first by [].
change (@mapping_multiplicity R X Y f A y=@mapping_multiplicity R X Y f C y).
by rewrite /mapping_multiplicity hEq.
Qed.
