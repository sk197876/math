(** Federer (1969), 4.1.9, p. 363: both original
    endpoint pushforwards exist under the single
    closed-cylinder properness hypothesis. Apply the
    preceding fixed-time theorem and the actual
    endpoint equalities on U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentProperSupport
  CurrentProperSupportMapAgreement CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyCylinder CurrentHomotopySliceProper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentHomotopyEndpointProper.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Variable A:set R.
Variables (U:set (R_n R n)) (V:set (R_n R nu)).
Variables (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu).
Hypothesis hGeometry:@is_current_homotopy_geometry R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hGeometry).
Variable T:@current_space R h2 n U hU j.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hGeometry T.
Local Notation initial_image := (@current_homotopy_endpoint_images R n nu A U V f g h hGeometry).1.
Local Notation final_image := (@current_homotopy_endpoint_images R n nu A U V f g h hGeometry).2.

(** Source for [current_homotopy_start_proper]: the
    original map f=h_0 is proper on spt T,
    supporting f#T in the current homotopy
    formula of Federer 4.1.9, p. 363.
    No separate endpoint properness is assumed. *)
Theorem current_homotopy_start_proper:
  @is_current_proper_on_support R h2 n nu j U hU V T f initial_image.
Proof.
have hZero:0<=(0:R)<=1 by rewrite lexx ler01.
have hSlice:=@current_homotopy_slice_proper R h2 n nu j A U V f g h hGeometry T
  0 hZero hProper.
exact:(@current_proper_support_map_agreement R h2 n nu j U V hU T
  (@current_homotopy_slice_map R n nu h 0) f _ initial_image
  (@current_homotopy_start R n nu A U V f g h hGeometry) hSlice).
Qed.

(** Source for [current_homotopy_end_proper]: the
    original map g=h_1 is proper on spt T,
    supporting g#T in the current homotopy
    formula of Federer 4.1.9, p. 363.
    The endpoint equality is used only on U. *)
Theorem current_homotopy_end_proper:
  @is_current_proper_on_support R h2 n nu j U hU V T g final_image.
Proof.
have hOne:0<=(1:R)<=1 by rewrite ler01 lexx.
have hSlice:=@current_homotopy_slice_proper R h2 n nu j A U V f g h hGeometry T
  1 hOne hProper.
exact:(@current_proper_support_map_agreement R h2 n nu j U V hU T
  (@current_homotopy_slice_map R n nu h 1) g _ final_image
  (@current_homotopy_end R n nu A U V f g h hGeometry) hSlice).
Qed.
End CurrentHomotopyEndpointProper.
