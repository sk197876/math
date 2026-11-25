(** Federer (1969), 4.1.20, p. 378: each coordinate
    projection of each scalar contraction is a top-degree
    flat current with Lebesgue-null support. By 4.1.18 it
    is zero; its volume action then kills every coordinate
    action of T. This is the original proof after its one
    orthogonal change of coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorIndices CoordinateProjection
  EuclideanCoordinateVolumes CurrentSpaces CurrentConstantFields CurrentContraction
  CurrentContractionSupport FlatCurrentsUP FlatCurrentFinite CurrentLipschitzCompactImage FlatCurrentSmoothContraction
  SmoothCompactSet CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentCompactPushforwardImages CurrentPushforwardSupport
  CurrentEuclideanLinearSmooth CurrentSmoothFlatImage CurrentTopFlatNullSupport
  CurrentCompactCoordinateZero CurrentCoordinateProjectedAction CurrentCompactSmoothZero
  CurrentCompactSmoothValue EuclideanLebesgueDimensions MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NullCoordinateProjections.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation UX:=(fun _:X=>True).
Local Notation UY:=(fun _:Y=>True).
Local Notation hX:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hY:=(fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Variable K:smooth_compact_set hNX UX.
Variable T:@current_space R h2 n UX hX m.
Hypothesis hFlat:@is_flat_current_supported_in R h2 n m UX hX K T.
Local Notation support:=(@current_support R h2 n UX hX m T).
Local Notation hT:=(@flat_supported_current_compact R h2 n m UX hX K T hFlat).

(** Source for [current_flat_null_coordinate_projections]:
    the coordinate part of Federer 4.1.20, p. 378, with
    the original flatness and null projection hypotheses.
    No normality, finite mass or integration representation
    of T is assumed; the necessary top-degree density is
    derived from the already proved 4.1.18 theorem. *)
Theorem current_flat_null_coordinate_projections:
  (forall lambda:Lambda n m,@euclidean_lebesgue_measure R m
    ((@coordinate_projection R n m lambda) @` support)=0)->T=0.
Proof.
move=>hNull.
apply:(@current_compact_coordinate_zero R h2 n m UX hX T hT)=>lambda gamma.
pose S:=@current_contraction R h2 n 0%N m UX hX gamma T.
have hSFlat:@is_flat_current_supported_in R h2 n m UX hX K S.
  exact:(@flat_current_smooth_contraction_supported R h2 n 0%N m
    UX hX K gamma T hFlat).
pose hS:=@flat_supported_current_compact R h2 n m UX hX K S hSFlat.
pose p:=hom_of_linear
  (GRing.Linear.clone _ _ _ _ (@coordinate_projection R n m lambda) _).
pose hImage:=fun (x:X) (_:True)=>Logic.I.
pose hClass:=@current_euclidean_linear_smooth R n m p UX hX.
pose Q:=@current_compact_map_pushforward R h2 n m UX UY hX hY
  p hImage hClass m S hS.
pose hQ:=@current_compact_map_image_compact R h2 n m UX UY hX hY
  p hImage hClass m S hS.
have hQFlat:@is_flat_current R h2 m m UY hY Q.
  exact:(@current_smooth_flat_image R h2 n m m UX UY hX hY
    p hImage hClass K S hSFlat).
have hSupport:@current_support R h2 m UY hY m Q `<=` p @` support.
  move=>y hy.
  have[x hx hxy]:=@current_pushforward_support_image R h2 n m m UX UY hX hY S
    p hImage hClass (@current_compact_map_proper R h2 n m m UX UY hX S
      p hImage (norm_class_continuous (hClass 0%N)) hS) y hy.
  exists x;last exact:hxy.
  exact:(@current_contraction_support_subset R h2 n 0%N m UX hX gamma T x hx).
have hQNull:@euclidean_lebesgue_measure R m
    (@current_support R h2 m UY hY m Q)=0.
  exact:(@measure_null_subset R Y (@euclidean_lebesgue_measure R m)
    (@euclidean_lebesgue_is_measure R m) _ _ hSupport (hNull lambda)).
have hZero:=@current_top_flat_null_support R h2 m UY hY Q hQFlat hQNull.
have hValue:=@current_coordinate_projected_action R h2 n m lambda T hT gamma hS.
have hZeroValue:=@current_compact_smooth_zero R h2 m m UY hY Q hQ hZero
  (@current_constant_form R h2 m UY hY m (@euclidean_volume_covector R m)).
rewrite -hValue /current_compact_smooth_value.
rewrite (@current_compact_smooth_value_independent R h2 m m UY hY Q _ hQ).
exact:hZeroValue.
Qed.
End NullCoordinateProjections.
