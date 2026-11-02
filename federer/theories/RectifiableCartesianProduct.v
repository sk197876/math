(** Federer (1969), 3.2.23, p. 260: the complete product
    theorem, exposing only independent rectifiability and measure laws.
    Actual first-factor rectifiability and the printed Borel hypotheses
    are retained. All natural dimensions use their existing conventions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Export RectifiableCartesianProductUP RectifiableCartesianMeasure.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap RectifiableSetUP RectifiableFiniteHausdorffMass
  RectifiableCartesianCover HausdorffMeasure MeasureUP MeasureRestriction MeasurePushforward
  MeasureSplit ProductMeasure ProductRectangleValue TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_cartesian_total_mass_from_identity]:
    the total-mass consequence of the displayed full-measure identity
    in Federer 3.2.23, p. 260. The product's whole-space
    rectangle law includes zero times infinity and degree zero;
    this supporting implication imposes no further set hypotheses. *)
Lemma rectifiable_cartesian_total_mass_from_identity (R:realType) (m mu n v:nat)
    (W:set (R_n R n)) (Z:set (R_n R v)):
  measure_pushforward (@euclidean_block_split R n v)
    (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu))
      (euclidean_cartesian_set W Z))=
  product_measure
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) W)
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu) Z) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu)
    (euclidean_cartesian_set W Z)=
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W*
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu Z.
Proof.
move=>hIdentity.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose alpha:=measure_restrict (@hausdorff_measure R X m) W.
pose beta:=measure_restrict (@hausdorff_measure R Y mu) Z.
pose hAlpha:=measure_restrict_is_measure (@hausdorff_measure_is_measure R X m) W.
pose hBeta:=measure_restrict_is_measure (@hausdorff_measure_is_measure R Y mu) Z.
have hEval:=congr1 (fun rho=>rho setT) hIdentity.
have hWhole:(@setT X) `*` (@setT Y)=setT.
  by apply/seteqP; split=>p; [move=>_|move=>_; split].
have hProduct:=product_measure_rectangle_value hAlpha hBeta
  (measure_measurable_whole hAlpha) (measure_measurable_whole hBeta).
rewrite hWhole in hProduct.
rewrite /measure_pushforward /measure_restrict preimage_setT setIT in hEval.
rewrite hEval hProduct /measure_restrict !setIT.
by [].
Qed.

(** Source for [rectifiable_cartesian_finite_hausdorff_mass]: the
    finite-mass part of the (H^(m+mu),m+mu)-rectifiability conclusion
    in Federer 3.2.23, p. 260, according to 3.2.14(4), p. 252.
    Actual first-factor rectifiability proves its finite mass;
    the target has exactly the printed finite-mass assumption. *)
Lemma rectifiable_cartesian_finite_hausdorff_mass (R:realType) (m mu n v:nat)
    (W:set (R_n R n)) (Z:set (R_n R v)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R v)) Z ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu)
    (euclidean_cartesian_set W Z)< +oo.
Proof.
move=>hW hWBorel hZ hZBorel.
have hMass:=rectifiable_cartesian_total_mass_from_identity
  (rectifiable_cartesian_measure_identity hW hWBorel hZ hZBorel).
have hFiniteW:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W)).
  exact:rectifiable_finite_hausdorff_mass hW.
have hFiniteZ:@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu Z \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (@hausdorff_measure_is_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z)).
  exact hZ.2.
rewrite hMass -(fineK hFiniteW) -(fineK hFiniteZ) -EFinM; exact:ltry.
Qed.

(** Source for [federer_3_2_23]: the complete theorem
    Federer 3.2.23, p. 260. An m-rectifiable Borel first
    factor and a finite-mass (H^mu,mu)-rectifiable Borel second
    factor have a finite-mass rectifiable Cartesian product, and
    its entire restricted Hausdorff measure is the product of
    their restricted measures. Every natural degree and zero-
    dimensional finite-set convention is retained. *)
Theorem federer_3_2_23 (R:realType) (m mu n v:nat)
    (W:set (R_n R n)) (Z:set (R_n R v)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R v)) Z ->
  is_rectifiable_cartesian_product m mu W Z.
Proof.
move=>hW hWBorel hZ hZBorel; constructor.
- split.
  + exact:(rectifiable_cartesian_countably_measure_rectifiable hW hZ.1).
  + exact:(rectifiable_cartesian_finite_hausdorff_mass hW hWBorel hZ hZBorel).
- exact:(rectifiable_cartesian_measure_identity hW hWBorel hZ hZBorel).
Qed.
