(** Federer (1969), 4.1.14, p. 371: the
    original locally Lipschitz deformation chain extends
    the smooth chain of 4.1.9, p. 363.
    Both are the actual interval-product image. Its
    support lies in the image of the original
    closed cylinder over sptT, under properness only
    on that cylinder. No mass assumption is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP
  NormLocalLipschitzScalarProduct CurrentSpaces FlatCurrentsUP
  CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyCylinder
  CurrentHomotopyTimeSegment CurrentHomotopyProductSupport
  CurrentDeformationChainSealed CurrentDeformationChainPushforward
  CurrentDomainTransport
  CurrentLocallyFlatTimeCylinder CurrentLipschitzHomotopyUP
  CurrentLipschitzDeformationChainUP CurrentLipschitzDeformationChainSealed CurrentLipschitzPushforwardUP
  CurrentLipschitzImageSmoothAgreement CurrentLipschitzImageSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_smooth_homotopy_locally_lipschitz]:
    an original smooth homotopy has the local
    Lipschitz class admitted in Federer 4.1.14,
    p. 371. The geometric component is the
    original one. Its current-space presentation is
    aligned internally below by the registered transport. *)
Definition current_smooth_homotopy_locally_lipschitz (R:realType)
    n nu (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hSmooth:@is_smooth_current_homotopy R n nu A U V f g h):
    @is_locally_lipschitz_current_homotopy R n nu A U V f g h:=
  conj hSmooth.1
    (@norm_class_one_locally_metric_lipschitz R (R_n R (1+n)%N) (R_n R nu)
      (inner_norm (@euclidean_inner_productP R (1+n)%N))
      (inner_norm (@euclidean_inner_productP R nu))
      (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))
      (inner_norm_real_norm (@euclidean_inner_productP R nu))
      (@current_homotopy_product_domain R n A U) h
      ((@norm_class_firstP R (R_n R (1+n)%N) (R_n R nu)
        (inner_norm (@euclidean_inner_productP R (1+n)%N))
        (inner_norm (@euclidean_inner_productP R nu))
        (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))
        (inner_norm_real_norm (@euclidean_inner_productP R nu))
        (@current_homotopy_product_domain R n A U) h).1 (hSmooth.2 1%N))).

Section CurrentLipschitzDeformationChainSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Variable A:set R.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variables f g:R_n R n->R_n R nu.
Variable h:R_n R (1+n)%N->R_n R nu.
Hypothesis hHomotopy:@is_locally_lipschitz_current_homotopy R n nu A U V f g h.
Local Notation geometry:=hHomotopy.1.
Local Notation hU:=(current_homotopy_source_open geometry).
Local Notation hV:=(current_homotopy_target_open geometry).
Local Notation hA:=(current_homotopy_parameter_interval geometry).
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation hAT:=(@current_homotopy_time_domain_open R A hA).
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Local Notation hAU:=(@current_cartesian_domain_open R 1%N n AT U hAT hU).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_locally_flat_current R h2 n m U hU T.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu m A U V f g h geometry T.
Local Notation interval:=(@current_homotopy_time_segment R A hA h2).
Local Notation product:=(@CartesianCurrentProduct.value R h2 1%N n 1%N m
  AT U hAT hU interval T).
Local Notation chain:=(@CurrentLipschitzDeformationChain.value R h2 n nu m
  A U V f g h hHomotopy T hT hProper).

(** Source for [current_lipschitz_deformation_chain_support]:
    the actual chain has support in the image
    of [0,1] times sptT, among the formal
    properties retained in Federer 4.1.14, p. 371,
    from 4.1.9, p. 363. T need only
    be locally flat; the cylinder may be noncompact. *)
Theorem current_lipschitz_deformation_chain_support:
  @current_support R h2 nu V hV (1+m)%N chain `<=`
    h @` (@current_homotopy_closed_cylinder R h2 n nu m
      A U V f g h geometry T).
Proof.
have hProduct:=@locally_flat_current_time_cylinder R h2 n m A U hA hU T hT.
have hProductProper:=@current_homotopy_product_proper R h2 n nu m
  A U V f g h geometry T hProper.
have hChain:=@CurrentLipschitzDeformationChain.laws R h2 n nu m
  A U V f g h hHomotopy T hT hProper.
have hSupport:=@current_lipschitz_image_support R h2 (1+n)%N nu (1+m)%N
  AU V hAU hV h (current_homotopy_image geometry) hHomotopy.2
  product hProduct hProductProper chain hChain.
move=>y hy.
have[z hz hzy]:=@hSupport y hy.
exists z;last exact:hzy.
exact:(@current_homotopy_product_support R h2 n nu m
  A U V f g h geometry T z hz).
Qed.
End CurrentLipschitzDeformationChainSupport.

(** Source for [current_chain_local_flat_openness_transport]:
    presenting the same original open domain by
    another openness proof preserves local flatness,
    supporting the smooth compatibility in Federer
    4.1.14, p. 371. This is the
    preceding equality transport of 4.1.11, p. 366. *)
Local Lemma current_chain_local_flat_openness_transport
    (R:realType) (h2:(1+1:R)!=0) n m (U:set (R_n R n))
    (hU hU':forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m):
  @is_locally_flat_current R h2 n m U hU T->
  @is_locally_flat_current R h2 n m U hU'
    (@current_domain_transport R h2 n U hU U (erefl U) hU' m T).
Proof.
have hProof:hU'=hU:=Prop_irrelevance _ _;subst hU'.
by rewrite current_domain_transport_refl.
Qed.

Section CurrentLipschitzChainGeometryTransport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Variable A:set R.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variables f g:R_n R n->R_n R nu.
Variable h:R_n R (1+n)%N->R_n R nu.
Local Notation Geometry:=(@is_current_homotopy_geometry R n nu A U V f g h).
Let sourceOpen (G:Geometry):=@current_homotopy_source_open R n nu A U V f g h G.
Let targetOpen (G:Geometry):=@current_homotopy_target_open R n nu A U V f g h G.
Let parameter (G:Geometry):=@current_homotopy_parameter_interval R n nu A U V f g h G.
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Let timeOpen (G:Geometry):=@current_homotopy_time_domain_open R A (parameter G).
Let productOpen (G:Geometry):=@current_cartesian_domain_open R 1%N n AT U
  (timeOpen G) (sourceOpen G).
Let interval (G:Geometry):=@current_homotopy_time_segment R A (parameter G) h2.
Let product (G:Geometry) (T:@current_space R h2 n U (sourceOpen G) m):=
  @CartesianCurrentProduct.value R h2 1%N n 1%N m AT U
    (timeOpen G) (sourceOpen G) (interval G) T.
Arguments product G T : clear implicits.

(** Source for [current_chain_homotopy_proper_geometry_transport]:
    the same literal cylinder and original map
    have the same properness with different proofs
    of their geometry, supporting Federer 4.1.14,
    p. 371. The current uses only the
    registered equal-domain transport. *)
Local Lemma current_chain_homotopy_proper_geometry_transport
    (G G':Geometry) (T:@current_space R h2 n U (sourceOpen G) m):
  @is_current_homotopy_proper R h2 n nu m A U V f g h G T->
  @is_current_homotopy_proper R h2 n nu m A U V f g h G'
    (@current_domain_transport R h2 n U (sourceOpen G) U (erefl U) (sourceOpen G') m T).
Proof.
have hGeometry:G'=G:=Prop_irrelevance _ _;subst G'.
by rewrite current_domain_transport_refl.
Qed.

(** Source for [current_chain_local_image_geometry_transport]:
    the original interval-product image law is
    unchanged by geometry evidence, supporting Federer
    4.1.14, p. 371. Equality transport identifies
    both actual current spaces; no new image
    or support hypothesis is introduced. *)
Local Lemma current_chain_local_image_geometry_transport
    (G G':Geometry)
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) AU h)
    (T:@current_space R h2 n U (sourceOpen G) m)
    (C:@current_space R h2 nu V (targetOpen G') (1+m)%N):
  @is_current_lipschitz_image R h2 (1+n)%N nu (1+m)%N AU V
    (productOpen G') (targetOpen G') h (current_homotopy_image G') hLocal
    (product G' (@current_domain_transport R h2 n U (sourceOpen G)
      U (erefl U) (sourceOpen G') m T)) C->
  @is_current_lipschitz_image R h2 (1+n)%N nu (1+m)%N AU V
    (productOpen G) (targetOpen G) h (current_homotopy_image G) hLocal
    (product G T)
    (@current_domain_transport R h2 nu V (targetOpen G') V (erefl V)
      (targetOpen G) (1+m)%N C).
Proof.
have hGeometry:G'=G:=Prop_irrelevance _ _;subst G'.
by rewrite !current_domain_transport_refl.
Qed.
End CurrentLipschitzChainGeometryTransport.

Section CurrentLipschitzDeformationChainSmooth.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Variable A:set R.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variables f g:R_n R n->R_n R nu.
Variable h:R_n R (1+n)%N->R_n R nu.
Hypothesis hSmooth:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry:=hSmooth.1.
Local Notation hU:=(current_homotopy_source_open geometry).
Local Notation hV:=(current_homotopy_target_open geometry).
Local Notation hA:=(current_homotopy_parameter_interval geometry).
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation hAT:=(@current_homotopy_time_domain_open R A hA).
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Local Notation hAU:=(@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation hLipschitz:=(@current_smooth_homotopy_locally_lipschitz R n nu
  A U V f g h hSmooth).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_locally_flat_current R h2 n m U hU T.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu m A U V f g h geometry T.
Local Notation interval:=(@current_homotopy_time_segment R A hA h2).
Local Notation product:=(@CartesianCurrentProduct.value R h2 1%N n 1%N m
  AT U hAT hU interval T).
Local Notation newGeometry:=hLipschitz.1.
Local Notation newSource:=(current_homotopy_source_open newGeometry).
Local Notation newTarget:=(current_homotopy_target_open newGeometry).
Local Notation newT:=(@current_domain_transport R h2 n U hU U (erefl U) newSource m T).
Local Notation newFlat:=(@current_chain_local_flat_openness_transport
  R h2 n m U hU newSource T hT).
Local Notation newProper:=(@current_chain_homotopy_proper_geometry_transport
  R h2 n nu m A U V f g h geometry newGeometry T hProper).
Local Notation rawChain:=(@CurrentLipschitzDeformationChain.value R h2 n nu m
  A U V f g h hLipschitz newT newFlat newProper).

(** Source for [current_lipschitz_deformation_chain_smooth_value]:
    present the actual new opaque chain in
    the original smooth current spaces, supporting
    Federer 4.1.14, p. 371. Only the
    registered equality transport changes proof metadata;
    the original domains, map and current are
    unchanged. No caller equality or transport premise occurs. *)
Definition current_lipschitz_deformation_chain_smooth_value:
    @current_space R h2 nu V hV (1+m)%N:=
  @current_domain_transport R h2 nu V newTarget V (erefl V) hV (1+m)%N rawChain.

(** Source for [current_lipschitz_deformation_chain_smooth_agreement]:
    the new chain equals the original smooth
    deformation chain of 4.1.9, p. 363,
    as required by the extension in Federer
    4.1.14, p. 371. The source remains
    any locally flat current with the printed
    closed-cylinder properness, including degree zero. *)
Theorem current_lipschitz_deformation_chain_smooth_agreement:
  current_lipschitz_deformation_chain_smooth_value=
  @CurrentDeformationChain.value R h2 n nu m
    A U V f g h hSmooth T hProper.
Proof.
have hProduct:=@locally_flat_current_time_cylinder R h2 n m A U hA hU T hT.
have hProductProper:=@current_homotopy_product_proper R h2 n nu m
  A U V f g h geometry T hProper.
have hCandidate:@is_current_lipschitz_image R h2 (1+n)%N nu (1+m)%N AU V hAU hV
    h (current_homotopy_image geometry) hLipschitz.2 product
    current_lipschitz_deformation_chain_smooth_value.
  exact (@current_chain_local_image_geometry_transport R h2 n nu m A U V f g h
    geometry newGeometry hLipschitz.2 T rawChain
    (@CurrentLipschitzDeformationChain.laws R h2 n nu m
      A U V f g h hLipschitz newT newFlat newProper)).
rewrite (@current_deformation_chain_pushforward R h2 n nu m
  A U V f g h hSmooth T hProper).
exact:(@current_lipschitz_image_smooth_agreement R h2 (1+n)%N nu (1+m)%N
  AU V hAU hV h (current_homotopy_image geometry) hLipschitz.2 hSmooth.2
  product hProduct
  (@current_homotopy_product_proper R h2 n nu m A U V f g h geometry T hProper)
  current_lipschitz_deformation_chain_smooth_value hCandidate).
Qed.
End CurrentLipschitzDeformationChainSmooth.

Arguments current_lipschitz_deformation_chain_smooth_value : clear implicits.
Arguments current_lipschitz_deformation_chain_smooth_agreement : clear implicits.
