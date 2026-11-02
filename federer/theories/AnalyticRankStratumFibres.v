(** Federer (1969), 3.2.33, p. 270: on the
    all-low-rank analytic branch the rank-mu stratum S
    lies in the original f inverse(Y). The corrected
    constant-rank reference is 3.1.18. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  RealNormUP NormClassOneUP NormClassOneActualField NormRegularity NormCoordinateSystemUP
  NormAnalyticRelativeUP NormAnalyticRelativeComposition NormAnalyticLocal
  AnalyticSubmanifoldUP AnalyticSubmanifoldCoordinateSystems EuclideanAnalyticDifferentialField
  RelativeLowImageLocus RelativeRankLocus AnalyticCoordinateRankLocus EuclideanMaximalRankGeneric
  CoordinateConstantRankFibreMass PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  RectifiablePositiveFibreCoareaUP RestrictedPositiveFibreComplement LinearRankUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_maximal_rank_stratum_positive_fibres]:
    the printed inclusion S in f inverse(Y), Federer
    3.2.33, p. 270. Actual analytic coordinate
    derivatives have the global upper rank bound; each
    exact-rank point is generic and its actual original
    fibre has positive complementary Hausdorff mass by
    3.1.18 (erratum p. 5, book p. 270 line 28).
    No chart, derivative field or fibre-positivity premise
    is supplied. Empty sets and all natural degrees remain. *)
Theorem analytic_maximal_rank_stratum_positive_fibres (R:realType) n mu l v
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  @is_euclidean_analytic_submanifold R n (mu+l) W ->
  @norm_analytic_relative R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) setT W F ->
  relative_low_image_locus mu W F = W ->
  let f:=partial_function_source_restrict W (partial_function_total F) in
  relative_rank_locus mu W F `<=`
    partial_function_preimage f (positive_partial_fibre_locus (mu+l) mu f).
Proof.
move=>hW hF hAll f x hxS.
have hx:W x:=hxS.1.1.
pose X:=R_n R n; pose Z:=R_n R (mu+l); pose Y:=R_n R v.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NZ:=inner_norm (@euclidean_inner_productP R (mu+l)).
pose NY:=inner_norm (@euclidean_inner_productP R v).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R (mu+l)).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R v).
have [T [V [phi [psi [hxT [hConvex [hPhi [hPsi hc]]]]]]]]:=
  analytic_submanifold_coordinate_system_exists hW hx.
have hCoordinate:=@relative_analytic_in_parametrisation R X Z Y NX NZ NY hNX hNZ hNY
  setT W V psi F (fun u hu=>(norm_coordinate_backward_membership hc hu).1) hPsi hF.
have [D [hD hDAnalytic]]:=euclidean_analytic_differential_field_exists hCoordinate.
have hField:is_norm_class_one_field NZ NY V (fun u=>F (psi u)) D.
  apply:(@norm_class_one_actual_field R Z Y NZ NY hNZ hNY V (fun u=>F (psi u)) D _ hD).
  exact:(norm_class_firstP hNZ hNY V (fun u=>F (psi u))).1
    (norm_analytic_class_all_orders hCoordinate 1%N).
have hCriterion q a (ha:W a) (ht:T a):relative_low_image_locus q W F a <->
    exists r,has_linear_rank (D (phi a)) r /\(r<=q)%N.
  exact:(@analytic_coordinate_low_image_iff R n (mu+l) v q W T V phi psi F D
    hc hPhi hPsi hF hD a ha ht).
have hRank:has_linear_rank (D (phi x)) mu:=
  (relative_rank_locus_coordinate_iff mu (fun q=>hCriterion q x hx hxT)).1 hxS.
have hBound u (hu:V u):exists r,has_linear_rank (D u) r /\(r<=mu)%N.
  have hBack:=norm_coordinate_backward_membership hc hu.
  have hLow:relative_low_image_locus mu W F (psi u) by rewrite hAll; exact hBack.1.
  have hRankU:=(hCriterion mu (psi u) hBack.1 hBack.2).1 hLow.
  by rewrite (norm_coordinate_cancel hc hu) in hRankU.
have hv:=norm_coordinate_forward_range hc hxT.
have hGeneric:=@euclidean_maximal_rank_generic R (mu+l) v mu V
  (fun u=>F (psi u)) D (phi x) hField (fun u hu=>@hBound u hu) hv hRank.
have hNonnull:=coordinate_constant_rank_fibre_nonnull hc hx hxT hField hGeneric.
case:(pselect (partial_function_preimage f (positive_partial_fibre_locus (mu+l) mu f) x))=>[hYes|hNo]; first exact hYes.
exfalso; apply:hNonnull.
have hNull:=@restricted_positive_fibre_complement_null R n v (mu+l) mu W F x hx hNo.
by rewrite addKn in hNull.
Qed.
