(** Federer (1969), 3.4.12, p. 339: opaque holomorphic
    germ operations exposed only through their original representative laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed HolomorphicGermUP
  HolomorphicGermOperationsUP HolomorphicGermOperationsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HolomorphicGermsSignature.
(** Source for [add]: holomorphic germ addition, 3.4.12, p. 339. *)
Parameter add:forall (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X),
  holomorphic_germ_space hNX a->holomorphic_germ_space hNX a->holomorphic_germ_space hNX a.
(** Source for [mul]: holomorphic germ multiplication, 3.4.12, p. 339. *)
Parameter mul:forall (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X),
  holomorphic_germ_space hNX a->holomorphic_germ_space hNX a->holomorphic_germ_space hNX a.
(** Source for [opp]: holomorphic germ negation, 3.4.12, p. 339. *)
Parameter opp:forall (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X),
  holomorphic_germ_space hNX a->holomorphic_germ_space hNX a.
(** Source for [laws]: the representative equations for the
    induced ring operations, 3.4.12, p. 339. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X),
  is_holomorphic_germ_operations (@add R X NX hNX a) (@mul R X NX hNX a) (@opp R X NX hNX a).
End HolomorphicGermsSignature.
Module HolomorphicGerms:HolomorphicGermsSignature.
(** Source for [add]: private addition witness from proved
    existence, 3.4.12, p. 339. *)
Definition add (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X):=
  projT1 (cid (@holomorphic_germ_operations_exists R X NX hNX a)).
(** Source for [mul]: private multiplication witness from the
    same existence proof, 3.4.12, p. 339. *)
Definition mul (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X):=
  projT1 (cid (projT2 (cid (@holomorphic_germ_operations_exists R X NX hNX a)))).
(** Source for [opp]: private negation witness from the
    same existence proof, 3.4.12, p. 339. *)
Definition opp (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X):=
  projT1 (cid (projT2 (cid (projT2 (cid (@holomorphic_germ_operations_exists R X NX hNX a)))))).
(** Source for [laws]: selected operations satisfy the
    independent original equations, 3.4.12, p. 339. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X):
  is_holomorphic_germ_operations (@add R X NX hNX a) (@mul R X NX hNX a) (@opp R X NX hNX a).
Proof.
exact:(projT2 (cid (projT2 (cid (projT2 (cid (@holomorphic_germ_operations_exists R X NX hNX a))))))).
Qed.
End HolomorphicGerms.
