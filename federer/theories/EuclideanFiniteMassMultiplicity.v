(** Federer (1969), 3.2.20, p. 257: supporting global
    finite multiplicity for a finite Hausdorff-mass source, obtained
    independently from 2.10.11, p. 176, and the Borel sandwich
    in 2.2.3, p. 61. It is a conclusion, not an extra area hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanMetricCompleteness
  EuclideanMetricSeparability ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  BorelRegularMeasureUP BorelRegularSandwich MeasurableFunctionUP MeasurableAlmostModification
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureFiniteUpperApproximant
  LipschitzUP HausdorffMeasure HausdorffClosedCoverAgreement HausdorffLipschitzImages LipschitzMultiplicityInteger
  MappingMultiplicity MappingMultiplicityLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_finite_mass_multiplicity]: supporting
    completed-measurable finite-source version of 2.10.11,
    p. 176, for the summation in Federer 3.2.20, p. 257.
    No rectifiability, extra Borel-source or target finite-mass
    hypothesis is needed. All natural degrees and ambient dimensions
    are retained, including degree zero. *)
Theorem euclidean_finite_mass_multiplicity (R : realType) n k m
    (F : inner_metric_space (@euclidean_inner_productP R n) ->
      inner_metric_space (@euclidean_inner_productP R k)) (W : set (R_n R n)) :
  is_metric_lipschitz setT F ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo ->
  is_measure_measurable_function
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) m)
    (partial_function_total (fun z=>(@mapping_multiplicity R _ _ F W z : extended_real_line R))) /\
  measure_almost_everywhere (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k)) m)
    [set z|@mapping_multiplicity R _ _ F W z< +oo].
Proof.
move=> hLip hW hFin.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R k).
pose mu := @hausdorff_measure R X m.
pose nu := @hausdorff_measure R Y m.
have hm := @hausdorff_measure_is_measure R X m.
have hn := @hausdorff_measure_is_measure R Y m.
have [L [hL hBound]] := hLip.
have [D [B [hDB [hBB [hDW [hWB hLoss]]]]]] :=
  borel_regular_finite_sandwich hm (@hausdorff_measure_borel_regular R X m) hW hFin.
have hBMass : mu B<=mu W.
  have hCover : B `<=` W `|` (B `\` D).
    move=> x hx; case: (pselect (W x))=> hw; first by left.
    right; split; first exact hx; move=> hd; exact: (hw (hDW x hd)).
  have hh := measure_binary_cover hm hCover; by rewrite hLoss adde0 in hh.
have hBFin : mu B< +oo := le_lt_trans hBMass hFin.
have hImage : nu (F @` (B `\` D))=0.
  have hh := hausdorff_lipschitz_image_bound m hBound (B `\` D).
  rewrite hLoss mule0 in hh; apply/eqP; rewrite eq_le hh (measure_nonnegative hn); reflexivity.
have [S [hSC hSD]] := euclidean_metric_separable R n.
have [hCount hEstimate] := @lipschitz_hausdorff_multiplicity_integer_bound R X Y F L m S B
  (@euclidean_metric_complete R n) hSC hSD hBound hBB.
have hB0 : 0<=mu B := @measure_nonnegative R X mu hm B.
have hBReal : mu B \is a fin_num by rewrite (ge0_fin_numE hB0).
have hValueFin : measure_lower_integral nu
    (partial_function_total (fun z=>(@mapping_multiplicity R X Y F B z : extended_real_line R)))< +oo.
  have hMass : (L^+m)%R%:E*mu B< +oo by rewrite -(fineK hBReal) -EFinM ltry.
  exact: (le_lt_trans hEstimate hMass).
have hUpper : measure_upper_integral nu
    (partial_function_total (fun z=>(@mapping_multiplicity R X Y F B z : extended_real_line R)))< +oo.
  have he := measure_upper_integral_unique (measure_upper_integral_specification _ _) hCount.2.1.
  by rewrite he.
have hFiniteB := finite_upper_integral_below_infinity_almost hn hUpper.
have hOutside : measure_almost_everywhere nu (~` (F @` (B `\` D))).
  by rewrite /measure_almost_everywhere setCK.
have hEqual z : ~ (F @` (B `\` D)) z ->
    @mapping_multiplicity R X Y F B z=@mapping_multiplicity R X Y F W z.
  move=> hz.
  have hBDE : B `<=` B by move=> x hx.
  have hFB := mapping_fibre_sandwich_equal hDW hWB hz.
  have hDD : D `<=` B := fun x hx=>hWB x (hDW x hx).
  have hFD := mapping_fibre_sandwich_equal hDD hBDE hz.
  by rewrite /mapping_multiplicity -hFB -hFD.
have hAE : measure_almost_equal nu
    (partial_function_total (fun z=>(@mapping_multiplicity R X Y F B z : extended_real_line R)))
    (partial_function_total (fun z=>(@mapping_multiplicity R X Y F W z : extended_real_line R))).
  apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _ hOutside)=> z hz.
  exists (@mapping_multiplicity R X Y F W z); split; last reflexivity; exact: hEqual.
split; first exact: (measurable_function_almost_equal hn hCount.1 hAE).
apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _
  (measure_almost_everywhere_and hn hOutside hFiniteB))=> z [hz [a [ha hFinA]]].
change (is_true (@mapping_multiplicity R X Y F W z< +oo)).
by rewrite -(hEqual z hz) (ha : @mapping_multiplicity R X Y F B z=a).
Qed.
