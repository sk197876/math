(** Federer (1969), 4.1.20, p. 378, third displayed
    equality: evaluate the projected scalar contraction on
    DY_1 wedge ... wedge DY_m by pulling that volume back
    to DX_lambda. Use the earlier proper smooth pushforward,
    compact smooth extension and actual contraction laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorIndices CoordinateProjection CovectorProducts
  EuclideanCoordinateForms EuclideanCoordinateVolumes CurrentSpaces CurrentConstantFields
  CurrentContraction SmoothCurrentFormProduct CurrentCompactContractionSmooth
  CurrentCompactMapProper CurrentPushforwardSealed CurrentPushforwardNormality
  CurrentCompactPushforwardSmooth CurrentCompactSmoothValue
  CurrentEuclideanLinearSmooth CurrentCoordinateProjectionSmoothVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section ProjectedAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable lambda:Lambda n m.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation UX:=(fun _:X=>True).
Local Notation UY:=(fun _:Y=>True).
Local Notation hX:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hY:=(fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Local Notation Compact:=(fun (T:@current_space R h2 n UX hX m)=>
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n UX hX m T)).
Variable T:@current_space R h2 n UX hX m.
Hypothesis hT:Compact T.
Variable gamma:@current_smooth_space R h2 n UX hX 0%N.
Local Notation S:=(@current_contraction R h2 n 0%N m UX hX gamma T).
Hypothesis hS:Compact S.
Local Notation p:=(hom_of_linear
  (GRing.Linear.clone _ _ _ _ (@coordinate_projection R n m lambda) _)).
Local Notation hImage:=(fun (x:X) (_:True)=>Logic.I).
Local Notation hClass:=(@current_euclidean_linear_smooth R n m p UX hX).
Local Notation hProper:=(@current_compact_map_proper R h2 n m m UX UY hX
  S p hImage (norm_class_continuous (hClass 0%N)) hS).
Local Notation Q:=(@CurrentPushforward.value R h2 n m m UX UY hX hY
  S p hImage hClass hProper).
Local Notation hQ:=(@current_pushforward_compact_support R h2 n m UX UY hX hY
  p hImage hClass m S hProper hS).
Local Notation volume:=(@current_constant_form R h2 m UY hY m
  (@euclidean_volume_covector R m)).
Local Notation coordinate:=(@current_constant_form R h2 n UX hX m
  (@omega_lambda R h2 X n (@euclidean_coordinate_form R n) m lambda)).

(** Source for [current_coordinate_projected_action]: the exact
    equality between the compact projected current's volume action
    and the original scalar-weighted coordinate action in Federer
    4.1.20, p. 378. Compactness has its original support meaning;
    no finite mass or density hypothesis is needed. *)
Theorem current_coordinate_projected_action:
  @current_compact_smooth_value R h2 m m UY hY Q hQ volume=
  @current_compact_smooth_value R h2 n m UX hX T hT
    (@smooth_current_form_product R h2 n 0%N m UX hX gamma coordinate).
Proof.
have hPush:=@current_compact_pushforward_smooth_value R h2 n m m UX UY hX hY
  p hImage hClass S hProper hS volume.
rewrite (@current_coordinate_projection_smooth_volume R h2 n m lambda UX hX) in hPush.
exact:(eq_trans hPush (@current_compact_contraction_smooth_value R h2 n 0%N m
  UX hX gamma T hT hS coordinate)).
Qed.
End ProjectedAction.
