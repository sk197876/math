(** Federer (1969), 4.1.14, p. 371: the opaque
    original locally Lipschitz deformation chain. Its independent actual
    pushforward action, existence and uniqueness precede
    this seal. The printed properness is imposed only
    on the closed time cylinder over spt T. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentHomotopyUP CurrentHomotopyCylinder
  FlatCurrentsUP CurrentLipschitzHomotopyUP
  CurrentLipschitzDeformationChainUP CurrentLipschitzDeformationChainExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CurrentLipschitzDeformationChainSignature.
(** Source for [value]: the original h#([0,1] times T)
    as an actual current of degree j+1, Federer
    4.1.14, p. 371. Only its public defining
    law is exposed. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_locally_lipschitz_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hT:@is_locally_flat_current R h2 n j U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) T)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T),
  @current_space R h2 nu V
    (@current_homotopy_target_open R n nu A U V f g h hHomotopy.1) (1+j)%N.
(** Source for [laws]: every admissible compact
    replacement computes the actual deformation-chain
    action, supporting Federer 4.1.14, p. 371. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_locally_lipschitz_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hT:@is_locally_flat_current R h2 n j U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) T)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T),
  @is_current_lipschitz_deformation_chain R h2 n nu j A U V f g h hHomotopy T
    (@value R h2 n nu j A U V f g h hHomotopy T hT hProper).
End CurrentLipschitzDeformationChainSignature.
Module CurrentLipschitzDeformationChain:CurrentLipschitzDeformationChainSignature.
(** Source for [value]: hide the proved actual
    deformation-chain witness of Federer 4.1.14,
    p. 371; the construction proves existence only. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_locally_lipschitz_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hT:@is_locally_flat_current R h2 n j U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) T)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T):
    @current_space R h2 nu V
      (@current_homotopy_target_open R n nu A U V f g h hHomotopy.1) (1+j)%N:=
  projT1 (cid (@current_lipschitz_deformation_chain_exists R h2 n nu j A U V f g h hHomotopy T hT hProper)).
(** Source for [laws]: the opaque witness satisfies
    its independently specified original action,
    supporting Federer 4.1.14, p. 371. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (n nu j:nat)
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_locally_lipschitz_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) j)
    (hT:@is_locally_flat_current R h2 n j U
      (@current_homotopy_source_open R n nu A U V f g h hHomotopy.1) T)
    (hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hHomotopy.1 T):
  @is_current_lipschitz_deformation_chain R h2 n nu j A U V f g h hHomotopy T
    (@value R h2 n nu j A U V f g h hHomotopy T hT hProper).
Proof.
exact:(projT2 (cid (@current_lipschitz_deformation_chain_exists R h2 n nu j A U V f g h hHomotopy T hT hProper))).
Qed.
End CurrentLipschitzDeformationChain.

Arguments CurrentLipschitzDeformationChain.value : clear implicits.

Arguments CurrentLipschitzDeformationChain.laws : clear implicits.
