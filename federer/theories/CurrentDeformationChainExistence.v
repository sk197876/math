(** Federer (1969), 4.1.9, p. 363: the original
    deformation chain exists for every current under
    properness of h on the closed time cylinder
    over its support. Reuse the preceding product
    and support-proper pushforward, as in the book. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentPushforwardExistence CurrentPushforwardSealed CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyCylinder CurrentHomotopyTimeSegment CurrentHomotopyProductSupport CurrentDeformationChainUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDeformationChainExistence.
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
Variable T:@current_space R h2 n U hU j.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T.
Local Notation time := (@current_homotopy_time_segment R A hInterval h2).
Local Notation product := (@CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU time T).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation product_proper := (@current_homotopy_product_proper R h2 n nu j A U V f g h
  geometry T hProper).
Local Notation law := (@is_current_deformation_chain R h2 n nu j A U V f g h hHomotopy T).

(** Source for [current_deformation_chain_exists]: the
    original h deformation chain is an actual current
    of degree j+1 under the printed cylinder
    properness, Federer 4.1.9, p. 363. Neither
    compact support nor a representation of T is assumed. *)
Theorem current_deformation_chain_exists:
  exists C:@current_space R h2 nu V hV (1+j)%N,law C.
Proof.
exists (@CurrentPushforward.value R h2 (1+n)%N nu (1+j)%N AU V hAU hV
  product h image hHomotopy.2 product_proper).
exact:(@CurrentPushforward.laws R h2 (1+n)%N nu (1+j)%N AU V hAU hV
  product h image hHomotopy.2 product_proper).
Qed.

(** Source for [current_deformation_chain_unique]: the
    original compact-replacement action determines the
    deformation chain uniquely, supporting Federer
    4.1.9, p. 363, by the preceding proper
    pushforward uniqueness theorem. *)
Theorem current_deformation_chain_unique (C D:@current_space R h2 nu V hV (1+j)%N):
  law C->law D->C=D.
Proof.
exact:(@current_pushforward_unique R h2 (1+n)%N nu (1+j)%N AU V hAU hV
  product h image hHomotopy.2 product_proper C D).
Qed.
End CurrentDeformationChainExistence.
