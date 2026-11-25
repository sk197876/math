(** Federer (1969), 4.1.9, p. 363: the original
    closed-cylinder properness implies properness of
    each slice on spt T for times between zero
    and one. Reuse the actual point inclusion of
    4.1.8, p. 362, and proper-map composition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentDomain CurrentSpaces CurrentProperSupport
  CurrentProperOnContainingSet CurrentCartesianDomain CurrentCartesianPointInclusion
  CurrentCartesianPointInclusionProper ProperMapUP ProperMapComposition ProperMapSmallerTarget
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain CurrentHomotopyCylinder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopySliceProper.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (1+n)%N).
Local Notation Y := (R_n R nu).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation ZT := (real_norm_metric_space hNZ).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hGeometry:@is_current_homotopy_geometry R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hGeometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h hGeometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Variable T:@current_space R h2 n U hU j.
Local Notation support := (@current_support R h2 n U hU j T).
Local Notation ST := [the topologicalType of set_type (support:set XT)].
Local Notation cylinder := (@current_homotopy_closed_cylinder R h2 n nu j A U V f g h hGeometry T).
Local Notation cylinder_in_domain := (@current_homotopy_cylinder_in_domain R h2 n nu j A U V f g h hGeometry T).
Local Notation image := (@current_homotopy_image R n nu A U V f g h hGeometry).
Variable t:R.
Hypothesis hBand:0<=t<=1.
Local Notation slice := (@current_homotopy_slice_map R n nu h t).

(** Source for [current_homotopy_band_slice_image]: the
    original fixed-time map takes U into V for
    each time in [0,1], supporting the pushed
    slice measures and endpoint currents in
    Federer 4.1.9, p. 363. *)
Definition current_homotopy_band_slice_image:forall x,U x->V (slice x):=
  @current_homotopy_slice_image R n nu A U V f g h hGeometry t
    (@current_homotopy_closed_time_band R A hInterval t hBand).

(** Source for [current_homotopy_slice_proper]: h_t is
    proper on the original spt T for every time
    between zero and one under the single printed
    cylinder hypothesis, supporting Federer 4.1.9,
    p. 363. No whole-domain properness is added. *)
Theorem current_homotopy_slice_proper:
  @is_current_homotopy_proper R h2 n nu j A U V f g h hGeometry T->
  @is_current_proper_on_support R h2 n nu j U hU V T slice
    current_homotopy_band_slice_image.
Proof.
move=>hProper.
have hAt:AT (@euclidean_one_embed R t).
  change (A (@euclidean_one_project R (@euclidean_one_embed R t))).
  rewrite euclidean_one_embedK.
  exact:(@current_homotopy_closed_time_band R A hInterval t hBand).
pose inclusion:=@current_cartesian_point_inclusion R 1%N n (@euclidean_one_embed R t).
pose inclusion_image:=fun x hx=>@current_cartesian_point_inclusion_image R 1%N n AT U
  (@euclidean_one_embed R t) hAt x hx.
pose inclusion_map:=@current_map_on_support R h2 n (1+n)%N j U hU AU T inclusion inclusion_image.
have hInclusionProper:is_proper_map inclusion_map.
  exact:(@current_cartesian_point_inclusion_proper R h2 1%N n j AT U hAT hU
    (@euclidean_one_embed R t) hAt T).
have hCylinderImage (x:ST):cylinder (set_val (inclusion_map x)).
  change (0<=@euclidean_one_project R
      (@euclidean_block_split R 1%N n
        (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,set_val x))).1<=1 /\
    support (@euclidean_block_split R 1%N n
      (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,set_val x))).2).
  rewrite euclidean_block_joinK euclidean_one_embedK.
  exact:conj hBand (set_valP x).
pose cylinder_map:=@proper_map_smaller_target_map ST ZT cylinder AU inclusion_map hCylinderImage.
have hCylinderProper:=@proper_map_smaller_target ST ZT cylinder AU cylinder_in_domain
  inclusion_map hCylinderImage hInclusionProper.
pose mapC:=@current_map_on_containing_set R (1+n)%N nu AU V cylinder cylinder_in_domain h image.
have hComposite:=@proper_map_composition ST
  [the topologicalType of set_type (cylinder:set ZT)] (current_domain R nu V)
  cylinder_map mapC hCylinderProper hProper.
have hEqual:mapC \o cylinder_map=
    @current_map_on_support R h2 n nu j U hU V T slice current_homotopy_band_slice_image.
  apply:funext=>x;apply:val_inj;by [].
change (is_proper_map (@current_map_on_support R h2 n nu j U hU V T slice
  current_homotopy_band_slice_image)).
by rewrite -hEqual.
Qed.
End CurrentHomotopySliceProper.
