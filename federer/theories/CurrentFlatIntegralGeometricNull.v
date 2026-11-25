(** Federer (1969), 4.1.20, p. 378: if m>0 and the
    original support of T in F_m(U) has zero I_1^m measure,
    then T=0. Include the compactly supported flat current
    in R^n, use the original orthogonal projection proof,
    and restrict the zero image back to U. The old compact
    inclusion and support laws supply this reduction. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  FlatCurrentsUP FlatCurrentFinite CurrentLipschitzCompactImage CurrentOpenIdentitySmooth CurrentOpenRestriction
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentCompactInclusionRestriction CurrentPushforwardSupport CurrentSmoothFlatImage
  CurrentFlatIntegralGeometricNullFull IntegralGeometricMeasure
  MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_flat_integral_geometric_null]: the
    original theorem of Federer 4.1.20, p. 378, for every
    open U and positive current degree. The support set is
    the actual original support, with no added measurability,
    normality, finite-mass or density-representation premise. *)
Theorem current_flat_integral_geometric_null (R:realType)
    (h2:(1+1:R)!=0) n m (hMN:(m<=n)%N)
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m):
  (0<m)%N->@is_flat_current R h2 n m U hU T->
  @integral_geometric_measure R n m hMN 1
    (@current_support R h2 n U hU m T)=0->T=0.
Proof.
move=>hPositive [K hFlat] hNull.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose Full:=fun _:X=>True.
pose hFull:=fun (x:X) (_:True)=>norm_full_domain_interior NX x.
pose image:=fun (x:X) (_:U x)=>Logic.I.
pose hClass:=@current_open_identity_smooth R n U hU.
pose hT:=@flat_supported_current_compact R h2 n m U hU K T hFlat.
pose Q:=@current_compact_map_pushforward R h2 n n U Full hU hFull
  (fun x:X=>x) image hClass m T hT.
have hQFlat:@is_flat_current R h2 n m Full hFull Q.
  exact:(@current_smooth_flat_image R h2 n n m U Full hU hFull
    (fun x:X=>x) image hClass K T hFlat).
have hSupport:@current_support R h2 n Full hFull m Q `<=`
    @current_support R h2 n U hU m T.
  move=>x hx.
  have[y hy hyx]:=@current_pushforward_support_image R h2 n n m U Full hU hFull T
    (fun x:X=>x) image hClass (@current_compact_map_proper R h2 n n m U Full hU T
      (fun x:X=>x) image (norm_class_continuous (hClass 0%N)) hT) x hx.
  by rewrite -hyx.
have hQNull:@integral_geometric_measure R n m hMN 1
    (@current_support R h2 n Full hFull m Q)=0.
  exact:(@measure_null_subset R X (@integral_geometric_measure R n m hMN 1)
    (@integral_geometric_measure_is_measure R n m hMN 1 (lexx 1)) _ _ hSupport hNull).
have hQZero:=@current_flat_integral_geometric_null_full R h2 n m hMN
  Q hPositive hQFlat hQNull.
have hRecover:=@current_compact_inclusion_restriction R h2 n U Full hU hFull
  image m T hT hClass (@current_compact_map_proper R h2 n n m U Full hU T
    (fun x:X=>x) image (norm_class_continuous (hClass 0%N)) hT).
change (@current_open_restriction R h2 n m U Full hU hFull image Q=T) in hRecover.
rewrite hQZero linear0 in hRecover;exact:esym hRecover.
Qed.
