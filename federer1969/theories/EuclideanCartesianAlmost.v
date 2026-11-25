(** Federer (1969), 3.2.23, p. 260: both factor differentials
    exist almost everywhere in the product parameters. The null
    cylinders are controlled directly by the rectangle law of 2.6.2,
    p. 115, and the Euclidean block measure of 2.6.5, p. 120. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric GrassmannAbbreviations
  EuclideanBlockCoordinates EuclideanBlockMeasure EuclideanLebesgueDimensions
  EuclideanCartesianMap MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure
  MeasureAlmostUP MeasureAlmostBasic MeasurePushforward ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_measure_almost_everywhere_factors]: supporting
    conull product domain for the Jacobian in Federer 3.2.23,
    p. 260. Null cylinder costs are zero even with an infinite
    opposite factor, by the convention in 2.6.1, pp. 114–115.
    Neither sigma finiteness nor measurability of the truth sets
    is required. Their exceptional complements are null measurable. *)
Lemma product_measure_almost_everywhere_factors (R:realType) (X Y:choiceType)
    (alpha:set X->\bar R) (beta:set Y->\bar R) (ha:is_measure alpha) (hb:is_measure beta)
    (P:set X) (Q:set Y):
  measure_almost_everywhere alpha P ->measure_almost_everywhere beta Q ->
  measure_almost_everywhere (product_measure ha hb) (P `*` Q).
Proof.
move=>hP hQ.
pose nu:=product_measure ha hb;have hn:=product_measure_is_measure ha hb.
have hLeft:nu ((~` P) `*` setT)=0.
  have hBound:=product_measure_rectangle_bound ha hb
    (measure_null_measurable ha hP) (measure_measurable_whole hb).
  rewrite hP mul0e in hBound.
  apply/eqP; by rewrite eq_le hBound (measure_nonnegative hn).
have hRight:nu (setT `*` (~` Q))=0.
  have hBound:=product_measure_rectangle_bound ha hb
    (measure_measurable_whole ha) (measure_null_measurable hb hQ).
  rewrite hQ mule0 in hBound.
  apply/eqP; by rewrite eq_le hBound (measure_nonnegative hn).
apply:(@measure_null_subset R [the choiceType of (X*Y)%type] nu hn
  (~` (P `*` Q)) (((~` P) `*` setT) `|` (setT `*` (~` Q))) _
  (measure_null_union hn hLeft hRight)).
move=>[x y] hNot.
have [hp|hp]:=pselect (P x).
- right; split; first exact Logic.I.
  move=>hq; apply:hNot; by split.
- left; split; [exact hp|exact Logic.I].
Qed.

(** Source for [euclidean_cartesian_almost_everywhere_factors]: supporting
    simultaneous actual differentiability in the product integral of
    Federer 3.2.23, p. 260. The block identification transfers the
    whole product conull statement, including either empty coordinate block. *)
Lemma euclidean_cartesian_almost_everywhere_factors (R:realType) m mu
    (P:set (R_n R m)) (Q:set (R_n R mu)):
  measure_almost_everywhere (@euclidean_lebesgue_measure R m) P ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R mu) Q ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R (m+mu))
    (euclidean_cartesian_set P Q).
Proof.
move=>hP hQ.
have hProduct:=product_measure_almost_everywhere_factors
  (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_is_measure R mu) hP hQ.
rewrite -euclidean_block_measure in hProduct.
exact hProduct.
Qed.
