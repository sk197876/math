(** Federer (1969), 4.1.9, p. 363: the opaque
    original deformation chain. Its independent actual
    pushforward action, existence and uniqueness precede
    this seal. The printed properness is imposed only
    on the closed time cylinder over spt T. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentHomotopyUP CurrentHomotopyCylinder
  CurrentDeformationChainUP CurrentDeformationChainExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentDeformationChainSignature.
(** Source for [value]: the original h#([0,1] times T)
    as an actual current of degree j+1, Federer
    4.1.9, p. 363. Only its public defining
    law is exposed. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T),
  @current_space R h2 nu V
    (@current_homotopy_target_open R n nu A U V f g h hHomotopy.1) (1+j)%N.
(** Source for [laws]: every admissible compact
    replacement computes the actual deformation-chain
    action, supporting Federer 4.1.9, p. 363. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T),
  @is_current_deformation_chain R h2 n nu j A U V f g h hHomotopy T
    (@value R h2 n nu j A U V f g h hHomotopy T hProper).
End CurrentDeformationChainSignature.
Module CurrentDeformationChain:CurrentDeformationChainSignature.
(** Source for [value]: hide the proved actual
    deformation-chain witness of Federer 4.1.9,
    p. 363; the construction proves existence only. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T):
    @current_space R h2 nu V
      (@current_homotopy_target_open R n nu A U V f g h hHomotopy.1) (1+j)%N:=
  projT1 (cid (@current_deformation_chain_exists R h2 n nu j A U V f g h hHomotopy T hProper)).
(** Source for [laws]: the opaque witness satisfies
    its independently specified original action,
    supporting Federer 4.1.9, p. 363. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T):
  @is_current_deformation_chain R h2 n nu j A U V f g h hHomotopy T
    (@value R h2 n nu j A U V f g h hHomotopy T hProper).
Proof.
exact:(projT2 (cid (@current_deformation_chain_exists R h2 n nu j A U V f g h hHomotopy T hProper))).
Qed.
End CurrentDeformationChain.
