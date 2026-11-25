(** Federer (1969), 3.2.48, p. 284: applying 3.2.23
    to the original completed measurable factors. The Borel theorem
    is transported across proved null differences, retaining genuine
    rectifiability of one factor as required by the printed argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanCartesianBorel
  RectifiableSetUP RectifiableElementary RectifiableClosure RectifiableFiniteHausdorffMass
  RectifiableBorelMeasureHull RectifiableCartesianProduct RectifiableProductNullSource
  RectifiableProductNullFactor MeasureRectifiableSubset
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureBasic MeasureRestriction
  MeasurePushforward MeasureNullModification MeasureAlmostBasic MeasurableAlmostModification
  MeasureHull HullSetAgreementConsequences BorelRegularMeasureUP BorelRegularSandwich
  TopologicalBorel BorelFamilyBasic ProductMeasure ProductMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_excess_equal_restrictions]: a proved
    null enlargement does not change any restriction value,
    by 2.1.2, p. 54, and 2.3.1, p. 72;
    supporting completed-factor products in 3.2.48, p. 284. *)
Lemma null_excess_equal_restrictions (R:realType) (X:choiceType)
    (mu:set X->\bar R) (A B:set X):
  is_measure mu ->A `<=` B ->mu (B `\` A)=0 ->
  measure_restrict mu A=measure_restrict mu B.
Proof.
move=>hm hAB hNull; apply:funext=>T.
apply:(@measure_null_modification_value R X mu hm (A `&` T) (B `&` T)
  (B `\` A) hNull)=>x hNot; split.
- by move=>[ha ht]; split; first exact (hAB x ha).
- move=>[hb ht]; split; last exact ht.
  apply:contrapT=>hna; exact (hNot (conj hb hna)).
Qed.

(** Source for [rectifiable_completed_cartesian_product]: the
    actual finite product and full restricted-measure equality
    used in 3.2.48, p. 284, extended from the Borel
    hypotheses of 3.2.23, p. 260, to completed measurable
    original factors. The genuinely rectifiable factor is retained
    in both null-product arguments; 3.2.24 is not bypassed. *)
Theorem rectifiable_completed_cartesian_product (R:realType) m mu n v
    (W:set (R_n R n)) (Z:set (R_n R v)):
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  is_rectifiable_cartesian_product m mu W Z /\
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu))
    (euclidean_cartesian_set W Z).
Proof.
move=>hW hWM hZ hZM.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose P:=inner_metric_space (@euclidean_inner_productP R (n+v)).
pose alpha:=@hausdorff_measure R X m.
pose beta:=@hausdorff_measure R Y mu.
pose rho:=@hausdorff_measure R P (m+mu).
pose hAlpha:=@hausdorff_measure_is_measure R X m.
pose hBeta:=@hausdorff_measure_is_measure R Y mu.
pose hRho:=@hausdorff_measure_is_measure R P (m+mu).
have [D [B [hDB [hBB [hDW [hWB hNullW]]]]]]:=
  @borel_regular_finite_sandwich R X alpha hAlpha (@hausdorff_measure_borel_regular R X m)
    W hWM (rectifiable_finite_hausdorff_mass hW).
pose W':=B `&` closure (W:set X).
have hW'B:@borel_set X W'.
  exact (borel_family_binary_intersection (borel_sets_family X) hBB (closed_borel_set (@closed_closure X W))).
have hW'R:@is_m_rectifiable R X m W'.
  exact (@rectifiable_subset R X m (closure (W:set X)) W' (fun x hx=>hx.2) (@rectifiable_closure R X m W hW)).
have hWW':W `<=` W'.
  move=>x hx; exact (conj (hWB x hx) (@subset_closure X W x hx)).
have hW'Null:alpha (W' `\` W)=0.
  apply:(measure_null_subset hAlpha _ hNullW)=>x [[hx _] hn]; split; first exact hx.
  move=>hD; exact (hn (hDW x hD)).
have [Z' [hZ'B [hHullZ hZ'R]]]:=rectifiable_borel_measure_hull hZ.
have hZZ':Z `<=` Z':=@measure_hull_subset R Y beta Z Z' hHullZ.
have hZ'Null:beta (Z' `\` Z)=0.
  exact (@measurable_hull_remainder_null R Y beta Z Z' hBeta hHullZ hZM).
have hBorelProduct:=@federer_3_2_23 R m mu n v W' Z' hW'R hW'B hZ'R hZ'B.
have hSourceSubset:euclidean_cartesian_set W Z `<=` euclidean_cartesian_set W' Z'.
  move=>p [hw hz]; exact (conj (hWW' _ hw) (hZZ' _ hz)).
have hBadFirst:rho (euclidean_cartesian_set (W' `\` W) Z')=0.
  exact (@rectifiable_product_null_source R m mu n v (W' `\` W) Z'
    (@rectifiable_subset R X m W' (W' `\` W) (fun x hx=>hx.1) hW'R)
    hW'Null hZ'R.1).
have hBadSecond:rho (euclidean_cartesian_set W' (Z' `\` Z))=0.
  exact (@rectifiable_product_null_factor R m n mu v W' (Z' `\` Z) hW'R hZ'Null).
have hProductNull:rho (euclidean_cartesian_set W' Z' `\` euclidean_cartesian_set W Z)=0.
  apply:(measure_null_subset hRho _ (measure_null_union hRho hBadFirst hBadSecond)).
  move=>p [[hwp hzp] hNot].
  case:(pselect (W (euclidean_block_split p).1))=>hw.
  - right; split; first exact hwp.
    split; first exact hzp; move=>hz; exact (hNot (conj hw hz)).
  - left; split; last exact hzp; exact (conj hwp hw).
have hRestriction:=null_excess_equal_restrictions hRho hSourceSubset hProductNull.
have hRestrW:=null_excess_equal_restrictions hAlpha hWW' hW'Null.
have hRestrZ:=null_excess_equal_restrictions hBeta hZZ' hZ'Null.
have hProductInputs:is_product_measure (measure_restrict alpha W) (measure_restrict beta Z)
    (product_measure (measure_restrict_is_measure hAlpha W') (measure_restrict_is_measure hBeta Z')).
  rewrite hRestrW hRestrZ; exact:product_measure_specification.
have hProductsEqual:=product_measure_unique hProductInputs
  (product_measure_specification (measure_restrict_is_measure hAlpha W)
    (measure_restrict_is_measure hBeta Z)).
split.
- constructor.
  + exact (@measure_rectifiable_subset R P rho (m+mu) _ _ hSourceSubset
      (rectifiable_cartesian_rectifiability_law hBorelProduct)).
  + rewrite hRestriction (rectifiable_cartesian_measure_law hBorelProduct).
    exact hProductsEqual.
- have hBigMeas:=borel_regular_borel_measurable hRho
    (@hausdorff_measure_borel_regular R P (m+mu)) (euclidean_cartesian_borel hW'B hZ'B).
  apply:(@measurable_set_null_modification R P rho hRho
    (euclidean_cartesian_set W' Z') (euclidean_cartesian_set W Z)
    (euclidean_cartesian_set W' Z' `\` euclidean_cartesian_set W Z) hProductNull _ hBigMeas).
  move=>p hNot; split.
  + move=>hp; apply:contrapT=>hn; exact (hNot (conj hp hn)).
  + exact (hSourceSubset p).
Qed.
