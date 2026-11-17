(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: Fubini transfers scalar convex-fibre subadditivity
    to the volume of an image with the remaining coordinates fixed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import InnerConvex ScalarConvexImageSumLength LebesgueScalarMeasure FibredScalarImageSection
  ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionBasic PartialExtendedArithmetic
  PartialExtendedOrderLoci MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralAddition MeasureIntegralComparison CountablyMeasurableUP ProductMeasure ProductSections ProductSetFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [fibred_scalar_image_sum_volume_bound]: an expanded
    helper for the continuity assertion of Federer 3.2.45,
    p. 279. Reuse Fubini, 2.6.2(3), p. 115, on the three
    actual image sets. Convex scalar fibres give the pointwise
    length bound. Product countable measurability and finite fibre
    lengths are explicit helper hypotheses, to be supplied by the
    actual compact linear images in its geometric application. *)
Theorem fibred_scalar_image_sum_volume_bound (R : realType) (X Y : choiceType)
    (alpha : set Y -> \bar R) (hAlpha : is_measure alpha)
    (A : set X) (b : X -> Y) (f g : X -> R) :
  let nu := product_measure hAlpha (lebesgue_scalar_is_measure R) in
  let C := fun u : X -> R => (fun x => (b x,u x)) @` A in
  measure_countably_measurable nu (C f) ->
  measure_countably_measurable nu (C g) ->
  measure_countably_measurable nu (C (fun x => (f x+g x)%R)) ->
  (forall y, @is_inner_convex R R^o (f @` [set x | A x /\ b x=y])) ->
  (forall y, @is_inner_convex R R^o (g @` [set x | A x /\ b x=y])) ->
  (forall y, lebesgue_scalar_measure (f @` [set x | A x /\ b x=y]) < +oo) ->
  (forall y, lebesgue_scalar_measure (g @` [set x | A x /\ b x=y]) < +oo) ->
  nu (C (fun x => (f x+g x)%R)) <= nu (C f) + nu (C g).
Proof.
move=> nu C hCF hCG hCS hFConvex hGConvex hFFinite hGFinite.
have hSection (u : X -> R) y :
    product_vertical_section (C u) y = u @` [set x | A x /\ b x=y].
  exact: fibred_scalar_image_vertical_section.
have hIF := (@product_set_fubini R Y R alpha (@lebesgue_scalar_measure R)
  hAlpha (lebesgue_scalar_is_measure R) (C f) hCF).2.2.1.
have hIG := (@product_set_fubini R Y R alpha (@lebesgue_scalar_measure R)
  hAlpha (lebesgue_scalar_is_measure R) (C g) hCG).2.2.1.
have hIS := (@product_set_fubini R Y R alpha (@lebesgue_scalar_measure R)
  hAlpha (lebesgue_scalar_is_measure R) (C (fun x => (f x+g x)%R)) hCS).2.2.1.
have hNu := product_measure_is_measure hAlpha (lebesgue_scalar_is_measure R).
have hNF : 0 <= nu (C f) := measure_nonnegative hNu (C f).
have hNG : 0 <= nu (C g) := measure_nonnegative hNu (C g).
have hAdd : extended_add (nu (C f)) (nu (C g)) = Some (nu (C f)+nu (C g)).
  by rewrite /extended_add ge0_adde_def.
have hSum := @measure_integral_add R Y alpha hAlpha _ _ _ _ _ hIF hIG hAdd.
apply: (@measure_integral_monotone R Y alpha hAlpha _ _ _ _ hIS hSum).
apply: (@measure_almost_everywhere_mono R Y alpha hAlpha setT _ _
  (measure_almost_everywhere_true hAlpha))=> y _.
pose F := lebesgue_scalar_measure (product_vertical_section (C f) y).
pose G := lebesgue_scalar_measure (product_vertical_section (C g) y).
exists (lebesgue_scalar_measure (product_vertical_section (C (fun x => (f x+g x)%R)) y)), (F+G).
split=> //; split.
- apply/partial_extended_function_add_graph; exists F,G; split=> //; split=> //.
  have hF : 0 <= F := measure_nonnegative (lebesgue_scalar_is_measure R) _.
  have hG : 0 <= G := measure_nonnegative (lebesgue_scalar_is_measure R) _.
  by rewrite /extended_add ge0_adde_def.
- rewrite /F /G !hSection.
  case: (eqVneq [set x | A x /\ b x=y] set0)=> [hEmpty|hNonempty].
  + by rewrite hEmpty !image_set0 (measure_empty (lebesgue_scalar_is_measure R)) adde0.
  + exact: scalar_convex_image_sum_length_bound ((set0P _).1 hNonempty)
      (hFConvex y) (hGConvex y) (hFFinite y) (hGFinite y).
Qed.
