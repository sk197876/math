(** Federer (1969), 4.1.9, p. 363: the original
    properness locus is the closed time interval
    times the actual current support. Its domain
    contains no additional points outside A times U. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentSpaces CurrentProperSupport CurrentCartesianDomain
  CurrentProperOnContainingSet ProperMapUP CurrentHomotopyUP
  CurrentHomotopyGeometry CurrentHomotopyDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyCylinder.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Z := (R_n R (1+n)%N).
Local Notation Y := (R_n R nu).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hGeometry:@is_current_homotopy_geometry R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hGeometry).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation hTime := (@current_homotopy_time_domain_open R A
  (@current_homotopy_parameter_interval R n nu A U V f g h hGeometry)).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n
  (@current_homotopy_time_domain R A) U hTime hU).
Variable T:@current_space R h2 n U hU j.
Local Notation p := (@euclidean_first_block_map R 1%N n).
Local Notation q := (@euclidean_last_block_map R 1%N n).

(** Source for [current_homotopy_closed_cylinder]: the exact
    original set {t:0<=t<=1} times spt T in
    the existing block coordinates, Federer 4.1.9,
    p. 363. The current may have noncompact support. *)
Definition current_homotopy_closed_cylinder:set Z:=
  [set z|0<=@euclidean_one_project R (p z)<=1 /\ @current_support R h2 n U hU j T (q z)].

(** Source for [current_homotopy_cylinder_in_domain]: the
    original closed cylinder is contained in A
    times U, supporting the precise properness
    hypothesis of Federer 4.1.9, p. 363. *)
Lemma current_homotopy_cylinder_in_domain:current_homotopy_closed_cylinder `<=` AU.
Proof.
move=>z [ht hx];split;last exact:hx.1.
exact:(@current_homotopy_closed_time_band R A
  (@current_homotopy_parameter_interval R n nu A U V f g h hGeometry)
  (@euclidean_one_project R (p z)) ht).
Qed.

(** Source for [is_current_homotopy_proper]: properness of
    the literal restriction h to the original closed
    cylinder, Federer 4.1.9, p. 363. This
    predicate imposes no properness on all A times U. *)
Definition is_current_homotopy_proper:Prop:=
  is_proper_map (@current_map_on_containing_set R (1+n)%N nu AU V
    current_homotopy_closed_cylinder current_homotopy_cylinder_in_domain h
    (@current_homotopy_image R n nu A U V f g h hGeometry)).

(** Source for [current_homotopy_contained_current_proper]:
    the original cylinder properness suffices for
    every current supported there, supporting the
    deformation chain and its boundary in Federer
    4.1.9, p. 363. This follows from the
    preceding relative-support restriction theorem. *)
Theorem current_homotopy_contained_current_proper k
    (S:@current_space R h2 (1+n)%N AU hAU k):
  (@current_support R h2 (1+n)%N AU hAU k S `<=` current_homotopy_closed_cylinder)->
  is_current_homotopy_proper->
  @is_current_proper_on_support R h2 (1+n)%N nu k AU hAU V S h
    (@current_homotopy_image R n nu A U V f g h hGeometry).
Proof.
exact:(@current_proper_on_containing_set R (1+n)%N nu AU V current_homotopy_closed_cylinder
  current_homotopy_cylinder_in_domain h
  (@current_homotopy_image R n nu A U V f g h hGeometry) h2 k hAU S).
Qed.
End CurrentHomotopyCylinder.
