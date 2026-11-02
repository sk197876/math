(** Federer (1969), 3.2.26(3), p. 262: integral-
    geometric and Hausdorff measure agree on every finite
    rectifiable source. The printed Borel reduction is
    expanded using Borel regularity of I_t and a true
    rectifiable Hausdorff measure hull. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableBorelMeasureHull CountablyMeasureRectifiableOperations
  RectifiableBorelGeometricLower RectifiableConvexGeometricUpper RectifiableGeometricBasicComparisons
  IntegralGeometricMeasure HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureHull BorelRegularMeasureUP BorelFamilyBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_integral_geometric_hausdorff_agreement]:
    full comparison (3) in 3.2.26, pp. 261–262,
    combined with I_t<=Q_t<=H^m. For nonmeasurable W,
    intersect a rectifiable Hausdorff hull with an I_t
    Borel cover of equal I_t mass. Monotonicity suffices;
    no difference between W and either hull is called null. *)
Theorem rectifiable_integral_geometric_hausdorff_agreement (R:realType) m n
    (hmn:(m<=n)%N) (W:set (R_n R n)) (t: \bar R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->1<=t ->
  @integral_geometric_measure R n m hmn t W=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W /\
  @convex_integral_geometric_measure R n m hmn t W=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W.
Proof.
move=>hRect ht.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose I:=@integral_geometric_measure R n m hmn t.
pose Q:=@convex_integral_geometric_measure R n m hmn t.
have hH:=@hausdorff_measure_is_measure R X m.
have hI:=@integral_geometric_measure_is_measure R n m hmn t ht.
have hQUpper:=@rectifiable_convex_geometric_upper R m n hmn W t hRect ht.
have hIQ:=@integral_geometric_le_convex R n m hmn t W ht.
have hLower:H W<=I W.
  have [M [hMBorel [hHull hMRect]]]:=rectifiable_borel_measure_hull hRect.
  have [B [hWB [hBBorel hIB]]]:=borel_regular_cover
    (@integral_geometric_measure_borel_regular R n m hmn t ht) W.
  pose S:=M `&` B.
  have hSBorel:@borel_set X S.
    exact:(borel_family_binary_intersection (borel_sets_family X) hMBorel hBBorel).
  have hSM:S `<=` M by move=>x [hx _].
  have hWS:W `<=` S by move=>x hx; split; [exact:measure_hull_subset hHull x hx|exact:hWB x hx].
  have hSRect:is_measure_m_rectifiable H m S.
    split; first exact:(@countably_measure_rectifiable_subset R X H m M S hSM hMRect.1).
    exact:(le_lt_trans (measure_mono hH hSM) hMRect.2).
  have hSLower:=@borel_rectifiable_geometric_lower R m n hmn S t hSRect hSBorel ht.
  have hSB:S `<=` B by move=>x [_ hx].
  change (I W=I B) in hIB.
  rewrite hIB; exact:(le_trans (measure_mono hH hWS) (le_trans hSLower (measure_mono hI hSB))).
split.
- apply/eqP; by rewrite eq_le (le_trans hIQ hQUpper) hLower.
- apply/eqP; by rewrite eq_le hQUpper (le_trans hLower hIQ).
Qed.
