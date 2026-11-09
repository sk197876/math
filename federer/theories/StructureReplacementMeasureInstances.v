(** Federer (1969), 3.3.16, p. 299: the four ACTUAL
    replacement measures satisfy the independent comparison laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureReplacementMeasureUP GrossOriginalProjectionBound ProjectionMeasure ExteriorMeasure
  IntegralGeometricMeasure HausdorffMeasure HausdorffSphericalComparison HausdorffDiameterCost
  GrossExteriorComparison ExteriorCompactCoverAgreement EuclideanExteriorLebesgue ExteriorConvexIntegralComparison
  RectifiableSetUP RectifiableFiniteHausdorffMass RectifiableGeometricMeasureEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [spherical_structure_replacement_laws]: actual
    spherical replacement in Federer 3.3.16, p. 299. Actual
    projection/Gross/exterior/Hausdorff comparisons give the
    uniform projection bound. Actual 3.2.26 gives image agreement. *)
Lemma spherical_structure_replacement_laws (R:realType) n m (hmn:(m<=n)%N):
  is_structure_replacement_measure m
    (@spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) m).
Proof.
constructor; [exact:spherical_measure_is_measure|exact:spherical_measure_borel_regular| |].
- exists 1%R; split; first exact:ltr01.
  move=>A p; rewrite mul1e.
  apply:le_trans (@gross_original_projection_bound R n m hmn A p) _.
  apply:le_trans (@federer_2_10_34 R n m hmn A) _.
  apply:le_trans (@exterior_measure_hausdorff_bound R n m A) _.
  exact:hausdorff_measure_le_spherical_measure.
- move=>A hA; exact:(@federer_3_2_26 R m n hmn A (rectifiable_hausdorff_measure_rectifiable hA)).1.
Qed.

(** Source for [exterior_structure_replacement_laws]: actual
    exterior-diameter replacement in Federer 3.3.16, p. 299.
    Actual 2.10.34 and 3.2.26 give the required laws, retaining
    every original subset and every natural degree. *)
Lemma exterior_structure_replacement_laws (R:realType) n m (hmn:(m<=n)%N):
  is_structure_replacement_measure m (@exterior_diameter_measure R n m).
Proof.
constructor; [exact:exterior_diameter_measure_is_measure|exact:exterior_diameter_measure_borel_regular| |].
- exists 1%R; split; first exact:ltr01.
  move=>A p; rewrite mul1e.
  exact:le_trans (@gross_original_projection_bound R n m hmn A p) (@federer_2_10_34 R n m hmn A).
- move=>A hA; exact:(@federer_3_2_26 R m n hmn A (rectifiable_hausdorff_measure_rectifiable hA)).2.1.
Qed.

(** Source for [gross_structure_replacement_laws]: actual Gross
    replacement in Federer 3.3.16, p. 299. Actual original
    projected-volume domination and 3.2.26 give the independent
    laws. Finite Gross mass need not imply finite Hausdorff mass. *)
Lemma gross_structure_replacement_laws (R:realType) n m (hmn:(m<=n)%N):
  is_structure_replacement_measure m (@gross_measure R n m).
Proof.
constructor; [exact:gross_measure_is_measure hmn|exact:gross_measure_borel_regular hmn| |].
- exists 1%R; split; first exact:ltr01.
  move=>A p; rewrite mul1e; exact:gross_original_projection_bound hmn A p.
- move=>A hA; exact:(@federer_3_2_26 R m n hmn A (rectifiable_hausdorff_measure_rectifiable hA)).2.2.1.
Qed.

(** Source for [convex_integral_structure_replacement_laws]:
    actual Q_t replacement in Federer 3.3.16, p. 299, for
    EVERY printed replacement exponent 1<=t<=infinity, not only
    infinity. The positive degree is the original 2.10.5
    convention. Actual 2.10.37 supplies a positive finite
    projection-comparison constant; actual 3.2.26 gives agreement. *)
Lemma convex_integral_structure_replacement_laws (R:realType) n m (hmn:(m<=n)%N) (t: \bar R):
  (0<m)%N ->1<=t ->is_structure_replacement_measure m
    (@convex_integral_geometric_measure R n m hmn t).
Proof.
move=>hm ht.
constructor; [exact:convex_integral_geometric_measure_is_measure ht|
  exact:convex_integral_geometric_measure_borel_regular ht| |].
- exists (hausdorff_normalisation R m*(m`!)%:R)%R; split.
  + apply:mulr_gt0; first exact:hausdorff_normalisation_positive.
    by rewrite ltr0n fact_gt0.
  + move=>A p.
    apply:le_trans (@gross_original_projection_bound R n m hmn A p) _.
    apply:le_trans (@federer_2_10_34 R n m hmn A) _.
    exact:(@exterior_convex_integral_geometric_bound R n m hmn t hm ht A).
- move=>A hA; exact:((@federer_3_2_26 R m n hmn A
    (rectifiable_hausdorff_measure_rectifiable hA)).2.2.2 t ht).1.
Qed.
