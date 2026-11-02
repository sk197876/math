(** Federer (1969), 3.2.28(2), p. 265:
    the actual coarea volume of the exterior-frame map. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps InnerProductUP InnerMetric
  OrthogonalMaps ExteriorGrading ExteriorNorm InnerExterior InnerExteriorPositivity AssociatedSubspace
  EuclideanHomInnerCharts EuclideanStiefelSmooth EuclideanStiefelCompact EuclideanStiefelVolumeDimensions
  EuclideanOrientedGrassmannSmooth EuclideanGrassmannCompact EuclideanExteriorWordSmooth
  EuclideanExteriorWordImage EuclideanExteriorPartialJacobian EuclideanExteriorFrameLipschitz
  EuclideanExteriorFrameFibres EuclideanExteriorFibreMeasure EuclideanSpecialOrthogonalMeasure
  FiniteInnerChartUP FiniteInnerSmoothSubmanifoldUP FiniteInnerCompactCoareaVolumes
  NormDifferentialUP HausdorffMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_exterior_coarea_volume]: the
    coarea identity preceding the displayed factor-two
    formula in Federer 3.2.28(2), p. 265.
    The Jacobian, compact rectifiability, actual fibre
    mass and coordinate invariance are proved, with no
    volume premise or selected global frame. *)
Theorem euclidean_exterior_coarea_volume (R:realType) m n:
  (0<m)%N ->(m<=n)%N ->
  let X:=inner_metric_space (@euclidean_hom_inner_productP R m n) in
  let Y:=inner_metric_space (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m) in
  @hausdorff_measure R X (m*(2*n-m-1)%/2)
    [set g|is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear g)]=
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R m m)) (m*(m-1)%/2)
    (@euclidean_special_orthogonal_set R m)*
  @hausdorff_measure R Y (m*(n-m))
    [set x|simple x /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) x= 1%R].
Proof.
move=>hm hmn X Y.
pose V:=Hom (R_n R m) (R_n R n).
pose U:=exterior_power (R_n R n) m.
pose B:=@euclidean_hom_inner_product R m n.
pose C:=@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
pose hB:=@euclidean_hom_inner_productP R m n.
pose hC:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m.
pose O:set V:=[set g|is_orthogonal_map (@euclidean_inner_product R m)
  (@euclidean_inner_product R n) (hom_as_linear g)].
pose GO:set U:=[set x|simple x /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) x= 1%R].
pose d:=(m*(2*n-m-1)%/2)%N.
pose q:=(m*(n-m))%N.
pose lambda:=@hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R m m))
  (m*(m-1)%/2) (@euclidean_special_orthogonal_set R m).
have [N [e [p [hChart hS]]]]:=inner_smooth_submanifold_class
  (@euclidean_stiefel_smooth_submanifold R m n) 1%N.
have [K [a [t [hTarget hT]]]]:=inner_smooth_submanifold_class
  (@euclidean_oriented_grassmann_smooth_submanifold R m n hm hmn) 1%N.
have hOrth:is_orthogonal_map C (@euclidean_inner_product R K) (hom_as_linear t).
  move=>x y; exact:(@finite_inner_chart_inverse_product R U C K a t hTarget x y).
have hDim:(q<=d)%N.
  by rewrite /q /d (euclidean_stiefel_dimension_split hmn) leq_addr.
have hLambda:0<=lambda:=measure_nonnegative
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_hom_inner_productP R m m)) (m*(m-1)%/2)) _.
have hValues g:O g ->exists D:Hom (R_n R N) (R_n R K),
    has_norm_differential (InnerNorm.inner_norm (@euclidean_inner_productP R N))
      (InnerNorm.inner_norm (@euclidean_inner_productP R K)) (fun _=>True)
      (fun z=>t (euclidean_exterior_word_map (e z))) (p g) D /\
    PartialExteriorNormUP.is_partial_exterior_norm q
      (PartialFunctionSourceRestriction.partial_function_source_restrict
        (TangentConeUP.norm_tangent_cone (InnerNorm.inner_norm (@euclidean_inner_productP R N)) (p @` O) (p g))
        (PartialFunctionBasic.partial_function_total D)) 1%R.
  move=>hG; have [L [_ [hDiff hNorm]]]:=@euclidean_exterior_partial_jacobian_one R m n N K e p t g
    hmn hChart hOrth hG.
  exists (hom_comp t (hom_comp L e)); by split.
have hMass y:GO y ->@hausdorff_measure R X (d-q) [set x|O x /\euclidean_exterior_word_map x=y]=lambda.
  move=>hy.
  have hImage:=@euclidean_exterior_word_image_simple_unit R m n hm.
  have [g hG <-]:((@euclidean_exterior_word_map R m n) @` O) y.
    rewrite /GO in hy; rewrite -hImage in hy; exact hy.
  rewrite /d /q (euclidean_exterior_fibre_dimension hmn).
  exact (@euclidean_exterior_frame_fibre_measure R m n g hG (m*(m-1)%/2)).
have hResult:=@finite_inner_compact_coarea_volumes R V U B C hB hC N K d q
  e p a t O GO (@euclidean_exterior_word_map R m n) 1%R lambda
  hChart hTarget hS hT (@euclidean_stiefel_compact R m n)
  (@euclidean_oriented_grassmann_compact R m n hm) hDim ler01 hLambda
  ltac:(exists m%:R; exact:euclidean_exterior_frame_lipschitz)
  ltac:(move=>g hG; exact:euclidean_exterior_word_frame_unit hG) hValues hMass.
by rewrite mul1e in hResult.
Qed.
