(** Federer (1969), 3.3.10, p. 296: the actual Fubini
    null-section and almost-everywhere zero-profile consequences. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic CountablyMeasurableUP
  ProductMeasure ProductSections ProductSetFubini MeasureIntegralUP MeasureIntegralUniqueness
  MeasureDensityNullSets MeasureNonnegativeZero PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_product_null_horizontal_sections]: the
    first product-nullity computation in Federer 3.3.10, p. 296,
    from actual 2.6.2 Fubini. All original horizontal sections are
    null; the original product set is countably measurable. No
    finiteness of the whole first-factor space is required. *)
Lemma structure_product_null_horizontal_sections (R:realType) (X Y:choiceType)
    (alpha:set X->\bar R) (beta:set Y->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta) (S:set (X*Y)):
  measure_countably_measurable (product_measure hAlpha hBeta) S ->
  (forall y,alpha (product_horizontal_section S y)=0) ->
  product_measure hAlpha hBeta S=0.
Proof.
move=>hS hSections.
have [_ [_ [_ hIntegral]]]:=@product_set_fubini R X Y alpha beta hAlpha hBeta S hS.
have hFunction:(fun y=>alpha (product_horizontal_section S y))=(fun _:Y=>0).
  apply:funext=>y; exact:hSections y.
rewrite hFunction in hIntegral.
exact:(measure_integral_unique hIntegral (measure_extended_zero_integral hBeta)).
Qed.

(** Source for [structure_product_null_vertical_sections]: the
    original triple-alternative remainder computation in Federer
    3.3.10, p. 296. Actual Fubini and everywhere null vertical
    sections imply product-nullity without global sigma finiteness. *)
Lemma structure_product_null_vertical_sections (R:realType) (X Y:choiceType)
    (alpha:set X->\bar R) (beta:set Y->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta) (S:set (X*Y)):
  measure_countably_measurable (product_measure hAlpha hBeta) S ->
  (forall x,beta (product_vertical_section S x)=0) ->
  product_measure hAlpha hBeta S=0.
Proof.
move=>hS hSections.
have [_ [_ [hIntegral _]]]:=@product_set_fubini R X Y alpha beta hAlpha hBeta S hS.
have hFunction:(fun x=>beta (product_vertical_section S x))=(fun _:X=>0).
  apply:funext=>x; exact:hSections x.
rewrite hFunction in hIntegral.
exact:(measure_integral_unique hIntegral (measure_extended_zero_integral hAlpha)).
Qed.

(** Source for [structure_product_null_horizontal_almost]: the
    last actual Fubini computation in Federer 3.3.10, p. 296.
    The original nonnegative horizontal mass profile has integral
    zero and is almost everywhere zero. All profile graph values
    and the original product set are retained. *)
Lemma structure_product_null_horizontal_almost (R:realType) (X Y:choiceType)
    (alpha:set X->\bar R) (beta:set Y->\bar R)
    (hAlpha:is_measure alpha) (hBeta:is_measure beta) (S:set (X*Y)):
  measure_countably_measurable (product_measure hAlpha hBeta) S ->
  product_measure hAlpha hBeta S=0 ->
  measure_almost_everywhere beta [set y|alpha (product_horizontal_section S y)=0].
Proof.
move=>hS hNull.
have [_ [_ [_ hIntegral]]]:=@product_set_fubini R X Y alpha beta hAlpha hBeta S hS.
rewrite hNull in hIntegral.
pose f:=partial_function_total (fun y:Y=>(alpha (product_horizontal_section S y):extended_real_line R)).
have hNonnegative:measure_almost_everywhere beta (partial_extended_nonnegative_locus f).
  apply:(@measure_almost_everywhere_mono R Y beta hBeta setT _ _
    (measure_almost_everywhere_true hBeta)).
  move=>y _; exists (alpha (product_horizontal_section S y)); split; first reflexivity.
  exact:measure_nonnegative hAlpha _.
have hEqual:=@nonnegative_integral_zero_almost_equal R Y beta hBeta f hIntegral hNonnegative.
apply:(@measure_almost_everywhere_mono R Y beta hBeta _ _ _ hEqual).
move=>y [z [hF hZero]].
change (alpha (product_horizontal_section S y)=z) in hF.
change (0=z) in hZero.
change (alpha (product_horizontal_section S y)=0).
by rewrite hF -hZero.
Qed.
