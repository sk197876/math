(** Federer (1969), 4.1.9, p. 363: specify
    the original deformation chain by its actual
    pushforward action. Existence under the printed
    cylinder properness and uniqueness are proved
    separately; this law assumes neither. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentPushforwardUP CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDeformationChainUP.
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
Local Notation time := (@current_homotopy_time_segment R A hInterval h2).
Local Notation product := (@CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU time T).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).

(** Source for [is_current_deformation_chain]: the original
    h#([0,1] times T), Federer 4.1.9, p. 363,
    satisfies the defining action on every compact
    replacement of the actual pullback near the
    product support. The chain has degree j+1. *)
Definition is_current_deformation_chain
    (C:@current_space R h2 nu V hV (1+j)%N):Prop:=
  @is_current_pushforward R h2 (1+n)%N nu (1+j)%N AU V hAU hV
    product h image hHomotopy.2 C.
End CurrentDeformationChainUP.
