(** Federer (1969), 3.4.12, p. 339: opaque actual
    germ derivatives with independent representative laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermJetsUP HolomorphicGermJetExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Module Type HolomorphicGermJetsSignature.
(** Source for [value]: the actual m-th differential of
    a holomorphic germ, 3.4.12, p. 339. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R)
  (hNX:is_real_norm NX) (a:X) m,holomorphic_germ_space hNX a->
  @ContinuousMultilinear.space R m (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (@complex_modulus R) hNX (@complex_modulus_real_norm R).
(** Source for [laws]: the actual differential at the centre
    of every original representative, 3.4.12, p. 339. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R)
  (hNX:is_real_norm NX) (a:X) m (alpha:holomorphic_germ_space hNX a),
  is_holomorphic_germ_jet alpha (@value R X NX hNX a m alpha).
End HolomorphicGermJetsSignature.
Module HolomorphicGermJets:HolomorphicGermJetsSignature.
(** Source for [value]: private choice of the unique jet
    whose existence was proved, 3.4.12, p. 339. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (a:X) m (alpha:holomorphic_germ_space hNX a):=
  projT1 (cid (@holomorphic_germ_jet_exists R X NX hNX a m alpha)).
(** Source for [laws]: the selected jet satisfies the
    independent all-representative laws, 3.4.12, p. 339. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (a:X) m (alpha:holomorphic_germ_space hNX a):
  is_holomorphic_germ_jet alpha (@value R X NX hNX a m alpha).
Proof. exact:(projT2 (cid (@holomorphic_germ_jet_exists R X NX hNX a m alpha))). Qed.
End HolomorphicGermJets.
