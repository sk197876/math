(** Federer (1969), 3.2.26, pp. 261–262: all
    six measures agree on a finite (H^m,m)-rectifiable
    subset of R^n. Retain arbitrary source sets and all
    exponents 1<=t<=infinity. Use the erratum p. 5:
    book p. 261 lines 22 and 29, and p. 262 line 14. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableSphericalMeasure RectifiableIntegralGeometricMeasure
  RectifiableGeometricBasicComparisons HausdorffMeasure IntegralGeometricMeasure
  ProjectionMeasure ExteriorMeasure EuclideanExteriorLebesgue GrossExteriorComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_26]: complete theorem
    3.2.26, p. 261, with proof on pp. 261–262.
    Spherical, exterior-diameter, Gross, convex integral-
    geometric and integral-geometric measure all equal
    Hausdorff measure. The basic chain I_infinity<=G<=T<=H
    avoids later comparison theorems and forward dependencies.
    No source measurability, chosen tangent field or cover
    calibration is an extra final premise. The existing
    natural-degree interfaces also include degree zero. *)
Theorem federer_3_2_26 (R:realType) m n (hmn:(m<=n)%N)
    (W:set (R_n R n)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W in
  @spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W=H /\
  @exterior_diameter_measure R n m W=H /\
  @gross_measure R n m W=H /\
  forall t: \bar R,1<=t ->
    @convex_integral_geometric_measure R n m hmn t W=H /\
    @integral_geometric_measure R n m hmn t W=H.
Proof.
move=>hRect H.
have hEquality t ht:=@rectifiable_integral_geometric_hausdorff_agreement R m n hmn W t hRect ht.
have hInfinity: @integral_geometric_measure R n m hmn +oo W=H:=(hEquality +oo (leey 1)).1.
have hIG:=@integral_geometric_infinity_gross_bound R n m hmn W.
have hGT:=@federer_2_10_34 R n m hmn W.
have hTH:=@exterior_measure_hausdorff_bound R n m W.
rewrite hInfinity in hIG.
split; first exact:rectifiable_spherical_hausdorff_agreement hRect.
split; first by apply/eqP; rewrite eq_le hTH (le_trans hIG hGT).
split; first by apply/eqP; rewrite eq_le (le_trans hGT hTH) hIG.
by move=>t ht; have [hI hQ]:=hEquality t ht; split.
Qed.
