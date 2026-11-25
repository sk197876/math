(** Federer (1969), 4.1.9, p. 363: opaque form homotopy
    operator on the actual smooth spaces. Its literal interval
    integral law is independent of the chosen compact localizations.
    Only the operator and its original value law are public. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentHomotopyUP
  CurrentHomotopyTransgressionUP CurrentHomotopyTransgressionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentHomotopyTransgressionSignature.
(** Source for [value]: the original smooth-form homotopy
    operator of Federer 4.1.9, p. 363. No chosen
    local cutoff or field representative is exposed. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h),
  Hom (@current_smooth_space R h2 nu V
    (@current_homotopy_target_open R n nu A U V f g h hHomotopy.1) (1+j))
    (@current_smooth_space R h2 n U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j).
(** Source for [laws]: every original point and multivector
    gives exactly the printed time integral, supporting
    Federer 4.1.9, p. 363. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h),
  @is_current_homotopy_transgression R h2 n nu j A U V f g h hHomotopy
    (@value R h2 n nu j A U V f g h hHomotopy).
End CurrentHomotopyTransgressionSignature.
Module CurrentHomotopyTransgression:CurrentHomotopyTransgressionSignature.
(** Source for [value]: seal the proved smooth linear
    homotopy witness, supporting Federer 4.1.9, p. 363. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h):
  Hom (@current_smooth_space R h2 nu V
    (@current_homotopy_target_open R n nu A U V f g h hHomotopy.1) (1+j))
    (@current_smooth_space R h2 n U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j):=
  projT1 (cid (@current_homotopy_transgression_exists R h2 n nu j A U V f g h hHomotopy)).
(** Source for [laws]: the opaque witness satisfies the
    independently specified literal interval law, supporting
    Federer 4.1.9, p. 363. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h):
  @is_current_homotopy_transgression R h2 n nu j A U V f g h hHomotopy
    (@value R h2 n nu j A U V f g h hHomotopy).
Proof. exact:(projT2 (cid (@current_homotopy_transgression_exists R h2 n nu j A U V f g h hHomotopy))). Qed.
End CurrentHomotopyTransgression.
