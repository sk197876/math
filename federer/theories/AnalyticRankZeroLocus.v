(** Federer (1969), 3.2.33, p. 270: actual
    analytic equations for the intrinsic low-rank locus. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP NormCoordinateSystemUP NormAnalyticUP NormAnalyticOperations NormAnalyticRelativeUP
  NormAnalyticRelativeComposition AnalyticSubmanifoldUP AnalyticSubmanifoldCoordinateSystems
  EuclideanHomOperator EuclideanAnalyticDifferentialField EuclideanExteriorGramRank
  EuclideanExteriorGramAnalytic RelativeLowImageLocus AnalyticCoordinateRankLocus AnalyticChartZeroLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_low_image_analytic_zero_locus]: the
    intrinsic condition dim im Df<=mu has actual local
    analytic equations, supporting Federer 3.2.33, p. 270.
    Analytic coordinates, their actual derivative field, and
    the proved Hilbert exterior Gram polynomial give all laws.
    No rank dichotomy, derivative field, null transport or
    global coordinate selection is supplied as a hypothesis. *)
Theorem relative_low_image_analytic_zero_locus (R:realType) n m v mu
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  @is_euclidean_analytic_submanifold R n m W ->
  @norm_analytic_relative R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) setT W F ->
  @is_analytic_chart_zero_locus R n m W (relative_low_image_locus mu W F).
Proof.
move=>hW hF; constructor; first by move=>x hx; exact hx.1.
move=>a ha.
have [T [V [phi [psi [haT [hConvex [hPhi [hPsi hc]]]]]]]]:=
  analytic_submanifold_coordinate_system_exists hW ha.
have hCoordinate:=@relative_analytic_in_parametrisation R (R_n R n) (R_n R m) (R_n R v)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R m))
  (inner_norm (@euclidean_inner_productP R v))
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R v)) setT W V psi F
  (fun u hu=>(norm_coordinate_backward_membership hc hu).1) hPsi hF.
have [D [hD hDAnalytic]]:=euclidean_analytic_differential_field_exists hCoordinate.
exists T,V,phi,psi,(fun u=>euclidean_exterior_gram mu.+1 (D u)).
split; first exact haT.
split; first exact hConvex.
split; first exact hc.
split.
- exact:(norm_analytic_compose_on (fun u hu=>Logic.I) hDAnalytic
    (@euclidean_exterior_gram_analytic R m v mu.+1)).
- move=>x hx ht.
  exact:(@analytic_coordinate_low_image_gram R n m v mu W T V phi psi F D
    hc hPhi hPsi hF hD x hx ht).
Qed.
