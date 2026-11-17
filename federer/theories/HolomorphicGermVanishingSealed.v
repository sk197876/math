(** Federer (1969), 3.4.12, p. 339: opaque
    set-germ ideals with the original local-vanishing laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric GermVanishingUP HolomorphicGermUP HolomorphicGermOperationsUP SetGermUP HolomorphicGermVanishingUP HolomorphicGermVanishingExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HolomorphicSetIdealSignature.
(** Source for [value]: ideal gamma_a(S), 3.4.12,
    p. 339, determined by its set germ. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:restricted_space (ComplexScalars.embed R) X->R)
  (hNX:is_real_norm NX) (a:X),
  @set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a->set (holomorphic_germ_space hNX a).
(** Source for [laws]: the independent all-representative
    membership law, 3.4.12, p. 339. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:restricted_space (ComplexScalars.embed R) X->R)
  (hNX:is_real_norm NX) (a:X) sigma,
  @is_holomorphic_set_ideal R X NX hNX a sigma (@value R X NX hNX a sigma).
End HolomorphicSetIdealSignature.
Module HolomorphicSetIdeal:HolomorphicSetIdealSignature.
(** Source for [value]: private choice of the proved
    unique membership set, 3.4.12, p. 339. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (a:X) sigma:=
  projT1 (cid (@holomorphic_set_ideal_exists R X NX hNX a sigma)).
(** Source for [laws]: the selected set satisfies the
    original vanishing law, 3.4.12, p. 339. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:restricted_space (ComplexScalars.embed R) X->R)
    (hNX:is_real_norm NX) (a:X) sigma:
  @is_holomorphic_set_ideal R X NX hNX a sigma (@value R X NX hNX a sigma).
Proof. exact:(projT2 (cid (@holomorphic_set_ideal_exists R X NX hNX a sigma))). Qed.
End HolomorphicSetIdeal.
