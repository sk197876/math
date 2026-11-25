(** Federer (1969), 3.4.3, p. 317: the local
    coordinate reduction to the tangent-critical estimate 3.4.2(9). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerConvex RealNormUP
  NormMetric NormDifferentialUP NormDifferentialLinear NormDifferentialChain NormDifferentialLocal
  NormDifferentialDirectional NormDifferentialFiniteCalculus NormClassOneUP NormRegularity
  NormRegularityOperations NormRegularityLinearMaps NormFiniteLinearBound NormDiffeomorphismUP
  LinearRankUP FiniteSourceLinearRank LinearRankImageInclusion
  EuclideanBlockLinearMaps RelativeClassUP PartialFunctionUP
  CriticalRankPrefixKernel CriticalOpenManifold CriticalFlatPiecesUP
  CriticalRelativeDifferentialLaws CriticalTangentImage RealHausdorffMeasure RealHausdorffMeasureLaws
  MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_chart_rank_reduction]: the commutative
    diagram and concluding application of 3.4.2(9) in
    3.4.3, p. 317. Differentiate L F(u,v)=u,
    transfer the actual rank bound through the local inverse,
    and prove that g(B) belongs to the original tangent-critical
    set. The final measure concerns f(B), without replacing
    either set by a measurable hull. *)
Theorem critical_chart_rank_reduction (R:realType) nu l k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (U S B:set (R_n R (nu+l))) (f:R_n R (nu+l)->Y)
    (g G:R_n R (nu+l)->R_n R (nu+l)) (L:Hom Y (R_n R nu))
    (hp:0<=nu%:R+l%:R/k%:R):
  (1<=k)%N ->(0<l)%N ->is_inner_convex S ->
  is_norm_diffeomorphism
    (inner_norm_real_norm (@euclidean_inner_productP R (nu+l)))
    (inner_norm_real_norm (@euclidean_inner_productP R (nu+l))) U S g G k ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R (nu+l))) hNY U f k ->
  B `<=` U ->norm_bounded_linear NY (inner_norm (@euclidean_inner_productP R nu)) L ->
  (forall x,U x ->euclidean_first_block (g x)=L (f x)) ->
  (forall x,B x ->exists D:Hom (R_n R (nu+l)) Y,
    has_norm_differential (inner_norm (@euclidean_inner_productP R (nu+l))) NY U f x D /\
    exists r,has_linear_rank D r /\(r<=nu)%N) ->
  @real_hausdorff_measure R (real_norm_metric_space hNY)
    (nu%:R+l%:R/k%:R) hp (f @` B)=0%E.
Proof.
move=>hk hl hConvex hChart hf hBU hL hPrefix hRankB.
pose X:=R_n R (nu+l);pose V:=R_n R nu.
pose NX:=inner_norm (@euclidean_inner_productP R (nu+l)).
pose NV:=inner_norm (@euclidean_inner_productP R nu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (nu+l)).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R nu).
pose P:=@euclidean_first_block_map R nu l.
pose F:=fun y=>f (G y).
have hGClass:=norm_diffeomorphism_inverse_class hChart.
have hGU y (hy:S y):U (G y):=norm_diffeomorphism_inverse_maps hChart hy.
have hF:norm_class hNX hNY S F k:=norm_class_compose_on hGU hGClass hf.
have [DF hDF]:=(norm_class_firstP hNX hNY S F).1 (norm_class_lower hk hF).
have [DG hDG]:=(norm_class_firstP hNX hNX S G).1 (norm_class_lower hk hGClass).
have hSOpen y (hy:S y):norm_domain_interior NX S y:=(norm_class_continuous hF hy).1.
have hPBound:=@norm_finite_linear_bounded R X V NX NV hNX hNV (nu+l)
  (@coordinate_basis R (nu+l)) (@coordinate_basisP R (nu+l)) P.
have hLF y (hy:S y):L (F y)= P y.
  have h:=hPrefix (G y) (hGU y hy).
  rewrite (norm_diffeomorphism_right_inverse hChart hy) in h;exact:esym h.
have hPrefixDF y (hy:S y) z:L (DF y z)= P z.
  have hActual:=norm_class_one_differential hDF hy.
  have hPost:=norm_differential_postcompose hNX hActual hL.
  have hSameFunction:=norm_differential_domain_agreement hNX hLF hPost.
  have hLinear:=@norm_differential_linear R X V NX NV hNX hNV S y P (hSOpen y hy) hPBound.
  have hEqual:=norm_differential_unique hNX hNV hSameFunction hLinear.
  have h:=congr1 (fun M:Hom X V=>M z) hEqual.
  exact:h.
have [Z hZ]:=@critical_vertical_plane_exists R nu l.
have hOmega:=@critical_open_manifold_family R (nu+l) l Z k S hk hConvex hSOpen.
have hRelative:norm_class_relative hNX hNY S S F k.
  move=>y hy;exists S,F;split;first exact:hy.
  split;first exact:hF.
  by move=>z hz _;split.
have hDimension:((nu+l)-l<nu+l)%N by rewrite addnK -{1}[nu]addn0 ltn_add2l.
have hDegree:(((nu+l)-l)%:R+((nu+l)-((nu+l)-l))%:R/k%:R:R)=nu%:R+l%:R/k%:R.
  by rewrite addnK addKn.
have hpOriginal:0<=(((nu+l)-l)%:R+((nu+l)-((nu+l)-l))%:R/k%:R:R) by rewrite hDegree.
have hNull:=@critical_tangent_critical_image_nullity R (nu+l) l Z (nu+l) k S Y NY hNY F
  hpOriginal hOmega hDimension hRelative.
have hNullOriginal:@real_hausdorff_measure R (real_norm_metric_space hNY)
    (nu%:R+l%:R/k%:R) hp (F @` critical_tangent_zero_locus hNY (grassmann_val Z) S F)=0%E.
  move:hpOriginal hNull;rewrite hDegree.
  move=>hProof hZero;rewrite (bool_irrelevance hp hProof);exact:hZero.
apply:(measure_null_subset (@real_hausdorff_measure_is_measure R (real_norm_metric_space hNY)
  (nu%:R+l%:R/k%:R) hp) _ hNullOriginal).
move=>y [x hx <-].
have hxU:=hBU x hx.
have hxS:S (g x):=norm_diffeomorphism_maps hChart hxU.
have hGg:G (g x)=x:=norm_diffeomorphism_left_inverse hChart hxU.
have [D [hD [r [hRank hr]]]]:=hRankB x hx.
have hDatG:has_norm_differential NX NY U f (G (g x)) D by rewrite hGg.
have hChain:=norm_differential_chain hNX hNX hNY
  (norm_class_one_differential hDG hxS) hDatG.
have hChainS:=@norm_differential_restrict R X Y NX NY
  (fun z=>S z /\U (G z)) S F (g x) (hom_comp D (DG (g x)))
  (fun z hz=>conj hz (hGU z hz)) (hSOpen (g x) hxS) hChain.
have hDFEqual:DF (g x)=hom_comp D (DG (g x)):=norm_differential_unique hNX hNY
  (norm_class_one_differential hDF hxS) hChainS.
have [s [hRankF hs]]:=finite_source_linear_rank_exists (DF (g x)) (@coordinate_basisP R (nu+l)).
have hRankOrder:(s<=r)%N.
  apply:(linear_rank_image_inclusion hRankF hRank).
  move=>v;exists (DG (g x) v);by rewrite hDFEqual hom_compE.
have hKill:=@critical_rank_prefix_kernel R nu l Y (DF (g x)) L s hRankF
  (leq_trans hRankOrder hr) (hPrefixDF (g x) hxS).
have [DRelative [hGraph hGraphE]]:=@critical_relative_differential_from_extension R X Y NX NY hNX hNY
  S S F F (g x) (DF (g x)) hxS (fun z _ _=>erefl) (norm_class_one_differential hDF hxS).
exists (g x).
- split;first exact:hxS.
  exists DRelative;split;first exact:hGraph.
  move=>z v hz hv.
  have hValue:=(hGraphE z v).1 hv.
  rewrite (hKill z ((hZ z).1 hz)) in hValue.
  exact:esym hValue.2.
- by rewrite /F hGg.
Qed.
