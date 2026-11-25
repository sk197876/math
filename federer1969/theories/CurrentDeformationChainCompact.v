(** Federer (1969), 4.1.9, p. 363: compact source
    currents give compactly supported deformation chains.
    Reuse the actual product support, exact original closed
    cylinder and original pushforward support theorem. This
    supports the point-current deduction for smooth forms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces CurrentSupportGeometry
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentPushforwardNormality CurrentPushforwardSealed
  SmoothCompactSet CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment
  CurrentHomotopyCylinder CurrentHomotopyProductSupport CurrentHomotopyCompactCylinder
  CurrentDeformationChainSealed CurrentDeformationChainPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDeformationChainCompact.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Variable T:@current_space R h2 n U hU j.
Hypothesis hCompact:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n U hU j T).
Local Notation cylinder := (@current_homotopy_closed_cylinder R h2 n nu j A U V f g h geometry T).
Local Notation S := (@current_homotopy_time_segment R A hInterval h2).
Local Notation product := (@CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU S T).

(** Source for [current_homotopy_compact_product]: the original
    time-segment product has compact support when T does,
    supporting the point-current form argument in Federer
    4.1.9, p. 363. *)
Theorem current_homotopy_compact_product:
  @compact (real_norm_metric_space hNZ) (@current_support R h2 (1+n)%N AU hAU (1+j) product).
Proof.
pose K:=@Build_smooth_compact_set R Z NZ hNZ AU cylinder
  (@current_homotopy_cylinder_in_domain R h2 n nu j A U V f g h geometry T)
  (@current_homotopy_compact_cylinder R h2 n nu j A U V f g h hHomotopy T hCompact).
exact:(@current_support_compact_bound R h2 (1+n)%N (1+j) AU hAU K product
  (@current_homotopy_product_support R h2 n nu j A U V f g h geometry T)).
Qed.

(** Source for [current_deformation_chain_compact]: the actual
    original deformation chain of a compactly supported T
    is compactly supported, supporting Federer 4.1.9, p. 363.
    The statement permits every proof of the original cylinder
    properness; no properness outside that cylinder is assumed. *)
Theorem current_deformation_chain_compact
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T):
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
    (@current_support R h2 nu V hV (1+j)
      (@CurrentDeformationChain.value R h2 n nu j A U V f g h hHomotopy T hProper)).
Proof.
rewrite (@current_deformation_chain_pushforward R h2 n nu j A U V f g h hHomotopy T hProper).
exact:(@current_pushforward_compact_support R h2 (1+n)%N nu AU V hAU hV h
  (@current_homotopy_image R n nu A U V f g h geometry) hHomotopy.2 (1+j) product
  (@current_homotopy_product_proper R h2 n nu j A U V f g h geometry T hProper)
  current_homotopy_compact_product).
Qed.
End CurrentDeformationChainCompact.
