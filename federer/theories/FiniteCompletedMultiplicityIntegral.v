(** Federer (1969), 2.5.10, p. 101: extending the Borel multiplicity formula
    of 2.10.10, p. 176, to finite H^1 measurable sets. The Borel sandwich
    2.2.3, p. 61, has null excess, so almost every fibre is unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureNonnegativeZero
  PartialExtendedOrderLoci MeasureIntegralAlmostEquality MeasureNullModification
  BorelRegularMeasureUP BorelRegularSandwich TopologicalBorel
  BorelDominatedMeasureTransfer MappingMultiplicity MappingMultiplicityLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_completed_multiplicity_integral]:
    supporting completed-set form of Federer 2.10.10,
    p. 176, needed for all summable functions in
    2.5.10, p. 101. The dominating measure mu
    is Borel regular; nu has the Borel multiplicity
    formula and satisfies nu<=mu. No assertion of
    global sigma-finiteness or Borelness of A is made. *)
Theorem finite_completed_multiplicity_integral (R : realType) (X : topologicalType)
    (Y : choiceType) (p : X -> Y) (mu nu : set X -> \bar R)
    (beta : set Y -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hb : is_measure beta) (hr : is_borel_regular_measure mu) :
  (forall S, nu S<=mu S) ->
  (forall S, borel_set S -> is_measure_integral beta
    (partial_function_total (fun y => (@mapping_multiplicity R X Y p S y : extended_real_line R))) (nu S)) ->
  forall A, measure_measurable mu A -> mu A < +oo ->
    is_measure_integral beta
      (partial_function_total (fun y => (@mapping_multiplicity R X Y p A y : extended_real_line R))) (nu A).
Proof.
move=> hd hB A hA hf.
have [D [B [hD [hB' [hDA [hAB hz]]]]]] := borel_regular_finite_sandwich hm hr hA hf.
have hn0 := @dominated_measure_null R X mu nu hn hd (B `\` D) hz.
have hi0 := hB (B `\` D) (borel_set_difference hB' hD).
rewrite hn0 in hi0.
have hp : measure_almost_everywhere beta
    (partial_extended_nonnegative_locus (partial_function_total
      (fun y => (@mapping_multiplicity R X Y p (B `\` D) y : extended_real_line R)))).
  apply: (@measure_almost_everywhere_mono R Y beta hb setT _ _ (measure_almost_everywhere_true hb))=> y _.
  exists (@mapping_multiplicity R X Y p (B `\` D) y); split=> //.
  exact: mapping_multiplicity_nonnegative.
have hae := @nonnegative_integral_zero_almost_equal R Y beta hb _ hi0 hp.
have he : nu D=nu A.
  apply: (@measure_null_modification_value R X nu hn D A (B `\` D) hn0)=> x hx.
  split; first exact: hDA.
  move=> hAx; apply: contrapT=> hDx; apply: hx; split=> //; exact: hAB.
rewrite -he; apply: (@measure_integral_almost_equal R Y beta hb _ _ _ (hB D hD)).
apply: (@measure_almost_everywhere_mono R Y beta hb _ _ _ hae)=> y [z [hz1 hz2]].
have hzero : @mapping_multiplicity R X Y p (B `\` D) y=0.
  change (@mapping_multiplicity R X Y p (B `\` D) y=z) in hz1.
  change (0=z) in hz2; by rewrite hz1 -hz2.
have hno := (@mapping_multiplicity_zero_iff R X Y p (B `\` D) y).1 hzero.
have hEq := @mapping_fibre_sandwich_equal X Y p D A B y hDA hAB hno.
exists (@mapping_multiplicity R X Y p D y); split=> //.
change (@mapping_multiplicity R X Y p A y=@mapping_multiplicity R X Y p D y).
by rewrite /mapping_multiplicity hEq.
Qed.
