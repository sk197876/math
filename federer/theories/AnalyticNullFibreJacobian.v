(** Federer (1969), 3.2.33, p. 270: on the
    global analytic low-rank branch, a null fibre forces
    the actual intrinsic mu-Jacobian to vanish. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  RealNormUP NormDifferentialUP NormDifferentialDirectional NormClassOneUP NormClassOneActualField
  NormRegularity NormCoordinateSystemUP NormAnalyticUP NormAnalyticLocal NormAnalyticRelativeUP
  NormAnalyticRelativeComposition AnalyticSubmanifoldUP AnalyticSubmanifoldCoordinateSystems
  EuclideanAnalyticDifferentialField EuclideanMaximalRankGeneric CoordinateConstantRankFibreMass
  LinearRankUP LinearRankAtLeast RelativeLowImageLocus AnalyticCoordinateRankLocus
  RelativeDifferentialUP RelativeCoordinateDifferential ParametricDifferentialUP
  PartialFunctionUP PartialExteriorNormUP ExteriorRankZero HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_null_fibre_relative_jacobian_zero]:
    the zero integrand outside f inverse(Y) on the
    all-low-rank branch of Federer 3.2.33, p. 270.
    Actual analytic coordinate derivatives have rank at most
    mu everywhere. A rank-mu point would have a positive
    complementary-dimensional fibre by the corrected 3.1.18
    appeal. Otherwise its rank is below mu and every
    actual exterior output word vanishes. No derivative,
    generic-point or positive-fibre premise is added. *)
Theorem analytic_null_fibre_relative_jacobian_zero (R:realType) n mu l v
    (W:set (R_n R n)) (F:R_n R n->R_n R v) x
    (d:partial_function (R_n R n) (R_n R v)):
  @is_euclidean_analytic_submanifold R n (mu+l) W ->
  @norm_analytic_relative R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) setT W F ->
  relative_low_image_locus mu W F = W ->W x ->
  @has_relative_norm_differential R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) setT W F x d ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) l
    [set z|W z /\F z=F x]=0%E ->
  is_partial_exterior_norm mu d 0.
Proof.
move=>hW hF hAll hx hRel hNull.
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
have hBound u (hu:V u):exists r,has_linear_rank (D u) r /\(r<=mu)%N.
  have hBack:=norm_coordinate_backward_membership hc hu.
  have hLow:relative_low_image_locus mu W F (psi u) by rewrite hAll; exact hBack.1.
  have hCriterion:=@analytic_coordinate_low_image_iff R n (mu+l) v mu W T V phi psi F D
    hc hPhi hPsi hF hD (psi u) hBack.1 hBack.2.
  have hRank:=hCriterion.1 hLow.
  by rewrite (norm_coordinate_cancel hc hu) in hRank.
have hv:V (phi x):=norm_coordinate_forward_range hc hxT.
have [r [hRank hrBound]]:=@hBound (phi x) hv.
have [E hE]:=(norm_class_firstP hNX hNZ T phi).1 (norm_analytic_class_all_orders hPhi 1%N).
have [J hJ]:=(norm_class_firstP hNZ hNX V psi).1 (norm_analytic_class_all_orders hPsi 1%N).
have [Q [hQ hParam]]:=(@relative_coordinate_differential_criterion R X Z Y
  NX NZ NY hNX hNZ hNY setT W T V phi psi F x (E x) (J (phi x)) d
  hc hx hxT (fun y hy=>Logic.I) (norm_class_one_differential hE hxT)
  (norm_class_one_differential hJ hv)).1 hRel.
have hEqual:Q=D (phi x):=norm_differential_unique hNZ hNY hQ (hD (phi x) hv).
rewrite hEqual in hParam.
case:(ltnP r mu)=>[hLess|hAtLeast].
- apply:(@partial_exterior_low_rank_norm_zero R (mu+l) n v mu (D (phi x)) d).
  + move=>hHigh.
    have hmu:=(linear_rank_at_leastP mu hRank).1 hHigh.
    by have:=leq_ltn_trans hmu hLess; rewrite ltnn.
  + move=>a b hab; have [u [_ hu]]:=(hParam a b).1 hab; by exists u.
- have he:r=mu by apply/eqP; rewrite eqn_leq hrBound hAtLeast.
  subst r.
  have hGeneric:=@euclidean_maximal_rank_generic R (mu+l) v mu V
    (fun u=>F (psi u)) D (phi x) hField (fun u hu=>@hBound u hu) hv hRank.
  have hNonNull:=coordinate_constant_rank_fibre_nonnull hc hx hxT hField hGeneric.
  exact:False_ind _ (hNonNull hNull).
Qed.
