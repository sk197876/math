(** Supporting linear changes of normal coordinates in Federer (1969),
    2.10.16, p. 178. An invertible change in the target replaces its fibres
    by the fibres at the inverse coordinate, and the pushforward measure
    supplies the integral scale. This uses 2.4.18(1), pp. 90–91, and the
    determinant measure law of 2.7.16, pp. 134–135. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MappingMultiplicity ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasurePushforward MeasureScaleIntegral
  PushforwardTotalNonnegativeIntegral MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bijective_postcomposition_fibre]: supporting
    fibre equality for the target change in 2.10.16, p. 178.
    This is elementary set theory: K(f(x))=z exactly when
    f(x)=G(z), for mutually inverse K and G. *)
Lemma bijective_postcomposition_fibre (X Y Z : Type) (f : X -> Y)
    (K : Y -> Z) (G : Z -> Y) A z :
  cancel K G -> cancel G K ->
  mapping_fibre (fun x => K (f x)) A z=mapping_fibre f A (G z).
Proof.
move=> hKG hGK; apply/seteqP; split=> x [hx he]; split=> //.
- by rewrite -he hKG.
- by rewrite he hGK.
Qed.

(** Source for [bijective_postcomposition_multiplicity_integral]:
    supporting scaled integral identity for the normal-coordinate
    change in 2.10.16, p. 178. The inverse pushforward
    and the base integral are explicit abstract hypotheses;
    the Euclidean application discharges them by the determinant
    formula. Infinite integral values are retained. *)
Theorem bijective_postcomposition_multiplicity_integral (R : realType)
    (X Y Z : choiceType) (f : X -> Y) (K : Y -> Z) (G : Z -> Y)
    (alpha : set Y -> \bar R) (beta : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (c : R) J :
  cancel K G -> cancel G K -> (0<c)%R ->
  measure_pushforward G beta=measure_scale c alpha ->
  is_measure_integral alpha
    (partial_function_total (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R))) J ->
  is_measure_measurable_function beta
    (partial_function_total (fun z => (@mapping_multiplicity R X Z (fun x => K (f x)) A z : extended_real_line R))) ->
  is_measure_integral beta
    (partial_function_total (fun z => (@mapping_multiplicity R X Z (fun x => K (f x)) A z : extended_real_line R)))
    (c%:E*J).
Proof.
move=> hKG hGK hc hpush hi hmeas.
have he : (fun z => (@mapping_multiplicity R X Z (fun x => K (f x)) A z : extended_real_line R))=
    (fun z => (@mapping_multiplicity R X Y f A (G z) : extended_real_line R)).
  apply/funext=> z; rewrite /mapping_multiplicity.
  by rewrite (bijective_postcomposition_fibre f A z hKG hGK).
rewrite he in hmeas *.
have [a [haX haY]] := @pushforward_total_nonnegative_integrals R Z Y beta hb G
  (fun y => (@mapping_multiplicity R X Y f A y : extended_real_line R))
  (fun y => @mapping_multiplicity_nonnegative R X Y f A y) hmeas.
rewrite hpush in haY.
have hs := @measure_scale_integral R Y alpha ha c hc _ J hi.
have hv := measure_integral_unique haY hs.
by rewrite -hv.
Qed.
