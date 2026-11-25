(** Federer (1969), 3.2.28(3), p. 266:
    actual coarea for S(g)=g alpha and spherical fibres. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric OrthogonalMaps
  EuclideanHomInnerCharts EuclideanStiefelSmooth EuclideanStiefelCompact EuclideanStiefelVolumeDimensions
  EuclideanFrameRestriction EuclideanFrameRestrictionLipschitz EuclideanForgetfulPartialJacobian
  EuclideanForgetfulFibreMeasure FiniteInnerChartUP FiniteInnerSmoothSubmanifoldUP FiniteInnerCompactCoareaVolumes
  NormDifferentialUP TangentConeUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialExteriorNormUP
  HausdorffMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_forgetful_coarea_volume]: the
    actual Jacobian-weighted coarea identity immediately
    before the volume recurrence in Federer 3.2.28(3),
    p. 266. The actual tangent Jacobian is
    (sqrt 2)^(-k), and actual fibres are unit
    spheres in R^(n-k), with m=k+1<=n.
    All auxiliary adapted-frame hypotheses are discharged. *)
Theorem euclidean_forgetful_coarea_volume (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1)):
  (k.+1<=n)%N ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1) (hom_as_linear alpha) ->
  let X:=inner_metric_space (@euclidean_hom_inner_productP R k.+1 n) in
  let Y:=inner_metric_space (@euclidean_hom_inner_productP R k n) in
  ((Num.sqrt (2:R))^-k)%:E*
    @hausdorff_measure R X (k.+1*(2*n-k.+1-1)%/2)
      [set g|is_orthogonal_map (@euclidean_inner_product R k.+1) (@euclidean_inner_product R n) (hom_as_linear g)]=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n-k))) (n-k-1)
      [set z|inner_norm (@euclidean_inner_productP R (n-k)) z= 1%R]*
    @hausdorff_measure R Y (k*(2*n-k-1)%/2)
      [set g|is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n) (hom_as_linear g)].
Proof.
move=>hkn hAlpha X Y.
pose V:=Hom (R_n R k.+1) (R_n R n).
pose U:=Hom (R_n R k) (R_n R n).
pose B:=@euclidean_hom_inner_product R k.+1 n.
pose C:=@euclidean_hom_inner_product R k n.
pose hB:=@euclidean_hom_inner_productP R k.+1 n.
pose hC:=@euclidean_hom_inner_productP R k n.
pose O:set V:=[set g|is_orthogonal_map (@euclidean_inner_product R k.+1) (@euclidean_inner_product R n) (hom_as_linear g)].
pose T:set U:=[set g|is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n) (hom_as_linear g)].
pose d:=(k.+1*(2*n-k.+1-1)%/2)%N.
pose q:=(k*(2*n-k-1)%/2)%N.
pose lambda:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n-k))) (n-k-1)
  [set z|inner_norm (@euclidean_inner_productP R (n-k)) z= 1%R].
have [N [e [p [hChart hS]]]]:=inner_smooth_submanifold_class
  (@euclidean_stiefel_smooth_submanifold R k.+1 n) 1%N.
have [K [a [t [hTarget hT]]]]:=inner_smooth_submanifold_class
  (@euclidean_stiefel_smooth_submanifold R k n) 1%N.
have hOrth:is_orthogonal_map C (@euclidean_inner_product R K) (hom_as_linear t).
  move=>x y; exact:(@finite_inner_chart_inverse_product R U C K a t hTarget x y).
have hSplit:(d=q+(n-k-1))%N:=euclidean_forgetful_dimension_split hkn.
have hDim:(q<=d)%N by rewrite hSplit leq_addr.
have hDegree:(d-q=n-k-1)%N by rewrite hSplit addKn.
have hLambda:0<=lambda:=measure_nonnegative
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R (n-k))) (n-k-1)) _.
have hJ:(0<=(Num.sqrt (2:R))^-k)%R by rewrite invr_ge0 exprn_ge0 // sqrtr_ge0.
have hValues g:O g ->exists D:Hom (R_n R N) (R_n R K),
    has_norm_differential (inner_norm (@euclidean_inner_productP R N))
      (inner_norm (@euclidean_inner_productP R K)) (fun _=>True)
      (fun z=>t (euclidean_frame_restriction n alpha (e z))) (p g) D /\
    is_partial_exterior_norm q
      (partial_function_source_restrict
        (norm_tangent_cone (inner_norm (@euclidean_inner_productP R N)) (p @` O) (p g))
        (partial_function_total D)) ((Num.sqrt (2:R))^-k).
  move=>hG; exists (hom_comp t (hom_comp (@euclidean_frame_restriction R k k.+1 n alpha) e)).
  exact:(@euclidean_forgetful_partial_jacobian R k n N K alpha e p t g hkn hChart hOrth hAlpha hG).
have hMass y:T y ->@hausdorff_measure R X (d-q)
    [set x|O x /\euclidean_frame_restriction n alpha x=y]=lambda.
  move=>hy; rewrite hDegree.
  exact:(@euclidean_forgetful_fibre_measure R k n alpha y
    (leq_trans (leqnSn k) hkn) hAlpha hy (n-k-1)).
exact:(@finite_inner_compact_coarea_volumes R V U B C hB hC N K d q e p a t O T
  (@euclidean_frame_restriction R k k.+1 n alpha) ((Num.sqrt (2:R))^-k) lambda
  hChart hTarget hS hT (@euclidean_stiefel_compact R k.+1 n) (@euclidean_stiefel_compact R k n)
  hDim hJ hLambda (@euclidean_frame_restriction_lipschitz R k k.+1 n alpha O)
  ltac:(move=>g hG; exact:euclidean_frame_restriction_orthogonal hAlpha hG) hValues hMass).
Qed.
