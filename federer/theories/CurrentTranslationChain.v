(** Federer (1969), 4.1.18, p. 374: the
    original fixed-translation deformation h_z#([0,1]
    times T) exists for every current. Equal-domain
    transport is kept internal; properness follows
    from the bounded displacement |z|. No compactness
    or measure representation of T is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormClassZeroTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps
  CurrentSpaces CurrentDomainTransport CurrentWholeSupportClosed
  ProperMapUP CurrentProperOnContainingSet CurrentCompactTimeCylinder
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyCylinder
  CurrentTranslationHomotopy CurrentTranslations EuclideanAdditiveGroup
  EuclideanBoundedDisplacementCylinderProper CurrentDeformationChainSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTranslationChain.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (1+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation C:=(@current_space R h2 n Full hFull m).
Variable z:X.
Local Notation Id:=(fun x:X=>x).
Local Notation tau:=(@euclidean_translation R n z).
Local Notation H:=(@current_translation_homotopy R n z).
Local Notation hH:=(@current_translation_homotopy_laws R n z).
Local Notation geometry:=hH.1.
Local Notation hSource:=(@current_homotopy_source_open R n n
  (fun _=>True) Full Full Id tau H geometry).
Local Notation hTarget:=(@current_homotopy_target_open R n n
  (fun _=>True) Full Full Id tau H geometry).

(** Source for [current_translation_chain_input]: an internal
    equality of original source presentations, supporting
    4.1.18, p. 374. Consumers see the original T. *)
Definition current_translation_chain_input (T:C):
    @current_space R h2 n Full hSource m:=
  @current_domain_transport R h2 n Full hFull Full (erefl _) hSource m T.
Local Notation Input:=current_translation_chain_input.

(** Source for [current_translation_chain_proper]: the original
    h_z is proper on the literal closed cylinder
    over spt T, as required by 4.1.9 and used
    in 4.1.18, p. 374. Supports may be unbounded. *)
Theorem current_translation_chain_proper (T:C):
  @is_current_homotopy_proper R h2 n n m (fun _=>True)
    Full Full Id tau H geometry (Input T).
Proof.
pose Support:=@current_support R h2 n Full hSource m (Input T).
have hClosed:=@current_whole_support_closed R h2 n m hSource (Input T).
have hContinuous:continuous (fun y:real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))=>
    (H y:real_norm_metric_space hNX)).
  move=>y;exact:(@norm_class_zero_continuous_at R Z X
    (inner_norm (@euclidean_inner_productP R (1+n)%N)) NX
    (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)) hNX
    (fun _=>True) H y
    (norm_class_continuous (@current_translation_homotopy_smooth_whole R n z 0%N)) Logic.I).
have hBound:forall y,@current_compact_time_cylinder_carrier R n Support y->
    NX (H y-@euclidean_last_block_map R 1%N n y)<=NX z.
  move=>y hy;exact:(@current_translation_homotopy_displacement R n z y hy.1).
have hProper:=@euclidean_bounded_displacement_cylinder_proper R n Support hClosed
  H hContinuous (NX z) hBound.
pose Cylinder:=@current_compact_time_cylinder_carrier R n Support.
pose AU:=@current_homotopy_product_domain R n (fun _=>True) Full.
pose Actual:=@current_map_on_containing_set R (1+n)%N n AU Full Cylinder
  (@current_homotopy_cylinder_in_domain R h2 n n m (fun _=>True)
    Full Full Id tau H geometry (Input T)) H
  (@current_homotopy_image R n n (fun _=>True) Full Full Id tau H geometry).
have hMap:Actual=@current_map_on_containing_set R (1+n)%N n
    (fun _=>True) Full Cylinder (fun _ _=>Logic.I) H (fun _ _=>Logic.I).
  apply:funext=>y;apply:val_inj;reflexivity.
change (is_proper_map Actual).
by rewrite hMap.
Qed.

(** Source for [current_translation_chain]: the actual old
    opaque deformation chain h_z#([0,1] times T),
    on the original whole Euclidean target in
    4.1.18, p. 374. No new construction is exposed. *)
Definition current_translation_chain (T:C):
    @current_space R h2 n Full hFull (1+m)%N:=
  @current_domain_transport R h2 n Full hTarget Full (erefl _) hFull (1+m)%N
    (@CurrentDeformationChain.value R h2 n n m (fun _=>True) Full Full
      Id tau H hH (Input T) (@current_translation_chain_proper T)).
End CurrentTranslationChain.
