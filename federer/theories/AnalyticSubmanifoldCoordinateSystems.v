(** Federer (1969), 3.2.33, p. 270: actual analytic
    coordinates on W and the intrinsic meaning of analytic f.
    The charts come from 3.1.19(4) and 3.1.24, pp. 231,240. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormDifferentialUP NormRegularity NormCoordinateSystemUP
  InnerConvex AnalyticSubmanifoldUP AnalyticSubmanifoldChartsUP AnalyticSubmanifoldCoordinates
  NormAnalyticUP NormAnalyticLocal NormAnalyticRelativeUP NormAnalyticRelativeComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_submanifold_coordinate_system_exists]:
    actual analytic coordinates used in Federer 3.2.33,
    p. 270. Both analytic maps and the convex parameter
    domain are retained. Their proved class-one laws and
    exact inverse identities give the existing abstract
    coordinate-system interface; no chart is selected globally. *)
Theorem analytic_submanifold_coordinate_system_exists (R:realType) n m
    (W:set (R_n R n)) a:
  @is_euclidean_analytic_submanifold R n m W ->W a ->
  exists T V (phi:R_n R n->R_n R m) (psi:R_n R m->R_n R n),
    T a /\is_inner_convex V /\
    @norm_analytic R (R_n R n) (R_n R m)
      (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R m)) T phi /\
    @norm_analytic R (R_n R m) (R_n R n)
      (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) V psi /\
    is_norm_coordinate_system (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R m)) W T V phi psi 1%N.
Proof.
move=>hW ha.
have [T [V [phi [psi [hTa [hConvex [hPhi [hPsi [hRange [hBack [hImage hCancel]]]]]]]]]]]:=
  analytic_submanifold_convex_coordinates hW ha.
exists T,V,phi,psi; split.
- exact:(norm_domain_interior_member (inner_norm_real_norm (@euclidean_inner_productP R n)) hTa).
- split; first exact hConvex.
  split; first exact hPhi.
  split; first exact hPsi.
  constructor=>//.
  + exact:(norm_analytic_class_all_orders hPhi 1%N).
  + exact:(norm_analytic_class_all_orders hPsi 1%N).
Qed.
