(** Federer (1969), 4.1.9, p. 363: the original
    cylinder properness gives the proper pushforward
    of [0,1] times T. Reuse the exact product
    support of 4.1.8, p. 360, and the actual
    time segment inside its original open interval. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces CurrentProperSupport
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianSupportEquality
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyCylinder CurrentHomotopyTimeSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyProductSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hGeometry:@is_current_homotopy_geometry R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hGeometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h hGeometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Variable T:@current_space R h2 n U hU j.
Local Notation S := (@current_homotopy_time_segment R A hInterval h2).
Local Notation product := (@CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU S T).
Local Notation cylinder := (@current_homotopy_closed_cylinder R h2 n nu j A U V f g h hGeometry T).

(** Source for [current_homotopy_product_support]: the
    actual product [0,1] times T has support
    contained in the original closed cylinder,
    supporting the precise properness hypothesis
    in Federer 4.1.9, p. 363. T is arbitrary. *)
Theorem current_homotopy_product_support:
  @current_support R h2 (1+n)%N AU hAU (1+j)%N product `<=` cylinder.
Proof.
move=>z hz.
rewrite (@current_cartesian_support R h2 1%N n 1%N j AT U hAT hU S T) in hz.
split;last exact:hz.2.
exact:(@current_homotopy_time_segment_support R A hInterval h2 _ hz.1).
Qed.

(** Source for [current_homotopy_product_proper]: the
    printed properness of h on the closed cylinder
    is sufficient to push forward the actual product,
    supporting the deformation chain of Federer
    4.1.9, p. 363. No compactness or integral
    representation of T is assumed. *)
Theorem current_homotopy_product_proper:
  @is_current_homotopy_proper R h2 n nu j A U V f g h hGeometry T->
  @is_current_proper_on_support R h2 (1+n)%N nu (1+j)%N AU hAU V product h
    (@current_homotopy_image R n nu A U V f g h hGeometry).
Proof.
exact:(@current_homotopy_contained_current_proper R h2 n nu j A U V f g h hGeometry T
  (1+j)%N product current_homotopy_product_support).
Qed.
End CurrentHomotopyProductSupport.
