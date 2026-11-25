(** Federer (1969), 4.1.14, pp. 371–372:
    for a compact flat source, the original
    locally Lipschitz deformation chain is the
    compact image of the exact interval-product
    flat current. This identifies the original
    chain for the subsequent sharp mass estimates. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet FlatCurrentsUP CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentLipschitzHomotopyUP
  CurrentLipschitzDeformationChainUP CurrentCompactTimeCylinder CurrentFlatTimeCylinder
  CurrentCompactLipschitzPushforwardUP
  CurrentLipschitzImageCompactAgreement CurrentFlatLipschitzPushforwardSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentLipschitzDeformationChainCompact.
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
Variable K:smooth_compact_set
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation KP:=(@current_compact_time_cylinder R n A U hA K).
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current_supported_in R h2 n m U hU K T.
Local Notation interval:=(@current_homotopy_time_segment R A hA h2).
Local Notation product:=(@CartesianCurrentProduct.value R h2 1%N n 1%N m
  AT U hAT hU interval T).
Variable C:@current_space R h2 nu V hV (1+m)%N.
Hypothesis hC:@is_current_lipschitz_deformation_chain R h2 n nu m
  A U V f g h hHomotopy T C.

(** Source for [current_lipschitz_deformation_chain_compact_image]:
    the original h#([0,1] times T) satisfies
    the full compact-image defining condition on
    the exact time-product index, Federer 4.1.14,
    pp. 371–372. All original smooth families
    remain quantified, and no normality or finite
    mass premise is imposed on T. *)
Theorem current_lipschitz_deformation_chain_compact_image:
  @is_current_compact_lipschitz_image R h2 (1+n)%N nu (1+m)%N AU V hAU hV
    h (current_homotopy_image geometry) hHomotopy.2 KP product C.
Proof.
have hProduct:=@flat_current_time_cylinder R h2 n m A U hA hU K T hFlat.
have hProductGlobal:@is_flat_current R h2 (1+n)%N (1+m)%N AU hAU product.
  by exists KP.
have hAgreement:=@current_lipschitz_image_compact_agreement R h2 (1+n)%N nu
  (1+m)%N AU V hAU hV h (current_homotopy_image geometry) hHomotopy.2
  product hProductGlobal C hC.
rewrite hAgreement.
exact:((@CurrentFlatLipschitzPushforward.laws R h2 (1+n)%N nu (1+m)%N
  AU V hAU hV h (current_homotopy_image geometry) hHomotopy.2
  product hProductGlobal).2 KP hProduct).
Qed.
End CurrentLipschitzDeformationChainCompact.
