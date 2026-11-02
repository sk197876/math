(** Federer (1969), 3.2.6, p. 246: zero
    multiplicity integral implies that the entire represented
    image is null. No measurability of the image is
    assumed for this inference. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureNonnegativeZero
  MappingMultiplicity MappingMultiplicityLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_multiplicity_integral_image_null]: the
    implication from the first equation with g=1 to
    N(f|A_3,y)=0 almost everywhere in Federer 3.2.6,
    p. 246. A nonempty fibre has nonzero counting mass. *)
Lemma null_multiplicity_integral_image_null (R:realType) (X Y:choiceType)
    (f:X->Y) (A:set X) (beta:set Y->\bar R) (hb:is_measure beta):
  is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f A y:extended_real_line R))) 0 ->
  beta (f @` A)=0.
Proof.
move=>hi.
pose u:=partial_function_total (fun y=>(@mapping_multiplicity R X Y f A y:extended_real_line R)).
have hp:measure_almost_everywhere beta (partial_extended_nonnegative_locus u).
  apply:(@measure_almost_everywhere_mono R Y beta hb _ _ _ (measure_almost_everywhere_true hb))=>y _.
  exists (@mapping_multiplicity R X Y f A y); split=>//; exact:mapping_multiplicity_nonnegative.
have hZero:=nonnegative_integral_zero_almost_equal hb hi hp.
apply:(@measure_null_subset R Y beta hb (f @` A)
  (~` partial_function_agreement u (partial_function_total (fun _:Y=>(0:extended_real_line R)))) _ hZero).
move=>y hy [z [hz h0]].
change (@mapping_multiplicity R X Y f A y=z) in hz.
change (0=z) in h0.
have hN:@mapping_multiplicity R X Y f A y=0 by rewrite hz -h0.
exact ((@mapping_multiplicity_zero_iff R X Y f A y).1 hN hy).
Qed.
