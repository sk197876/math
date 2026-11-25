(** Federer (1969), 4.1.20, p. 378: choose the
    original good orthogonal change of coordinates, apply
    the preceding top-degree projection argument to its
    actual image current, then recover T by the inverse
    orthogonal image. Every input flat current is allowed;
    its mass need not be finite. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorIndices CoordinateProjection
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure
  EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  CurrentSpaces FlatCurrentsUP FlatCurrentFinite CurrentLipschitzCompactImage SmoothCompactSet
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentPushforwardSupport CurrentEuclideanLinearSmooth CurrentSmoothFlatImage
  CurrentCompactInverseSupport CurrentFlatNullCoordinateProjections
  IntegralGeometricMeasure IntegralGeometricNullCoordinateRotation
  EuclideanLebesgueDimensions MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FullNullSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).

(** Source for [current_flat_integral_geometric_null_full]:
    the full-space proof of Federer 4.1.20, p. 378. The
    original integral-geometric support measure is zero;
    the finite family of good projections is a conclusion,
    not a new hypothesis. Flatness supplies compact support. *)
Theorem current_flat_integral_geometric_null_full
    (T:@current_space R h2 n Full hFull m):
  (0<m)%N->@is_flat_current R h2 n m Full hFull T->
  @integral_geometric_measure R n m hMN 1
    (@current_support R h2 n Full hFull m T)=0->T=0.
Proof.
move=>hPositive [K hFlat] hNull.
pose A:=@current_support R h2 n Full hFull m T.
pose hT:=@flat_supported_current_compact R h2 n m Full hFull K T hFlat.
have[g hGood]:=@integral_geometric_null_coordinate_rotation R n m hMN A hNull.
pose f:=orthogonal_element_map g.
pose inverse:=euclidean_rectangular_adjoint f.
pose hImage:=fun (x:X) (_:True)=>Logic.I.
pose hClass:=@current_euclidean_linear_smooth R n n f Full hFull.
pose hInverseClass:=@current_euclidean_linear_smooth R n n inverse Full hFull.
pose S:=@current_compact_map_pushforward R h2 n n Full Full hFull hFull
  f hImage hClass m T hT.
have hSFlat:@is_flat_current R h2 n m Full hFull S.
  exact:(@current_smooth_flat_image R h2 n n m Full Full hFull hFull
    f hImage hClass K T hFlat).
have hSupport:@current_support R h2 n Full hFull m S `<=` f @` A.
  exact:(@current_pushforward_support_image R h2 n n m Full Full hFull hFull T
    f hImage hClass (@current_compact_map_proper R h2 n n m Full Full hFull T
      f hImage (norm_class_continuous (hClass 0%N)) hT)).
have hSZero:S=0.
  have[L hL]:=hSFlat.
  apply:(@current_flat_null_coordinate_projections R h2 n m L S hL)=>lambda.
  apply:(@measure_null_subset R (R_n R m) (@euclidean_lebesgue_measure R m)
    (@euclidean_lebesgue_is_measure R m) _ _ _ (hGood lambda)).
  move=>y [z hz <-].
  have[x hx hfx]:=hSupport z hz.
  exists x;first exact:hx.
  by rewrite hfx.
have hOrthogonal:=orthogonal_element_orthogonal g.
exact:(@current_compact_inverse_image_zero R h2 n n m f inverse
  hClass hInverseClass
  (@euclidean_orthogonal_adjoint_cancel R n f hOrthogonal)
  T hT hSZero).
Qed.
End FullNullSupport.
