(** Federer (1969), 4.1.14, p. 371: the
    locally Lipschitz deformation chain exists and
    is unique under properness only on the
    closed time cylinder over the actual support.
    Reuse the independently proved local image
    and the normal interval times locally flat
    current product. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed FlatCurrentsUP
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyCylinder
  CurrentHomotopyTimeSegment CurrentHomotopyProductSupport
  CurrentLipschitzHomotopyUP CurrentLipschitzPushforwardUP
  CurrentLipschitzImageExistence CurrentLipschitzImageUniqueness
  CurrentLocallyFlatTimeCylinder CurrentLipschitzDeformationChainUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentLipschitzDeformationChainExistence.
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
Local Notation Chain:=(@is_current_lipschitz_deformation_chain R h2 n nu m
  A U V f g h hHomotopy T).

(** Source for [current_lipschitz_deformation_chain_exists]:
    the original locally Lipschitz homotopy has
    an actual deformation chain, Federer 4.1.14,
    p. 371. Every original noncompact locally
    flat source and support-cylinder proper map
    is admitted, without a measure representation. *)
Theorem current_lipschitz_deformation_chain_exists:
  exists C:@current_space R h2 nu V hV (1+m)%N,Chain C.
Proof.
have hProduct:=@locally_flat_current_time_cylinder R h2 n m A U hA hU T hT.
have hProductProper:=@current_homotopy_product_proper R h2 n nu m
  A U V f g h geometry T hProper.
exact:(@current_lipschitz_image_exists R h2 (1+n)%N nu (1+m)%N AU V hAU hV
  h (current_homotopy_image geometry) hHomotopy.2 product hProduct hProductProper).
Qed.

(** Source for [current_lipschitz_deformation_chain_unique]:
    the original deformation chain is unique by
    its literal local image action, supporting
    Federer 4.1.14, p. 371. *)
Theorem current_lipschitz_deformation_chain_unique
    (C D:@current_space R h2 nu V hV (1+m)%N):Chain C->Chain D->C=D.
Proof.
have hProduct:=@locally_flat_current_time_cylinder R h2 n m A U hA hU T hT.
have hProductProper:=@current_homotopy_product_proper R h2 n nu m
  A U V f g h geometry T hProper.
exact:(@current_lipschitz_image_unique R h2 (1+n)%N nu (1+m)%N AU V hAU hV
  h (current_homotopy_image geometry) hHomotopy.2 product hProduct hProductProper C D).
Qed.
End CurrentLipschitzDeformationChainExistence.
