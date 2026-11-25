(** Federer (1969), 4.1.14, p. 371: the
    original locally Lipschitz deformation chain is
    h#([0,1] times T). Specify it by
    the independent local-image laws; prove existence
    from local flatness and the original cylinder
    properness. No construction is assumed by the
    independent chain specification. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment
  CurrentLipschitzHomotopyUP CurrentLipschitzPushforwardUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentLipschitzDeformationChainUP.
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
Local Notation interval:=(@current_homotopy_time_segment R A hA h2).
Local Notation product:=(@CartesianCurrentProduct.value R h2 1%N n 1%N m
  AT U hAT hU interval T).

(** Source for [is_current_lipschitz_deformation_chain]:
    the literal image h#([0,1] times T),
    Federer 4.1.14, p. 371, has the
    original local-cutoff action and is locally
    flat. The defining local-image property is
    independent of a chosen chain or cutoff. *)
Definition is_current_lipschitz_deformation_chain
    (C:@current_space R h2 nu V hV (1+m)%N):Prop:=
  @is_current_lipschitz_image R h2 (1+n)%N nu (1+m)%N AU V hAU hV
    h (current_homotopy_image geometry) hHomotopy.2 product C.
End CurrentLipschitzDeformationChainUP.
