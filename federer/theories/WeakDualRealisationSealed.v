(** Federer (1969), 4.1.5, p. 349: opaque
    evaluation- and norm-preserving identification of
    the earlier weak dual with the actual abstract
    continuous dual. Only the proved laws are public. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP ContinuousDualUP VectorDaniellHypotheses
  WeakDualRealisationUP WeakDualRealisationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type WeakDualRealisationSignature.
(** Source for [value]: represent the original
    weak dual in the actual Y*, Federer 4.1.5,
    p. 349, using the proved public surjectivity. *)
Parameter value:forall (R:realType) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN),weak_dual_space hNY->D.
(** Source for [laws]: the exact original evaluation
    and norm laws, Federer 4.1.5, p. 349. *)
Parameter laws:forall (R:realType) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN),is_weak_dual_realisation ed DN (@value R Y NY hNY D ed DN hD).
End WeakDualRealisationSignature.
Module WeakDualRealisation:WeakDualRealisationSignature.
(** Source for [value]: choose the proved witness
    behind the interface, Federer 4.1.5, p. 349. *)
Definition value (R:realType) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN):weak_dual_space hNY->D:=
  projT1 (cid (@weak_dual_realisation_exists R Y NY hNY D ed DN hD)).
(** Source for [laws]: the hidden map has the
    independently specified original laws, Federer
    4.1.5, p. 349. *)
Lemma laws (R:realType) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (hD:is_continuous_dual hNY ed DN):is_weak_dual_realisation ed DN (@value R Y NY hNY D ed DN hD).
Proof. exact:(projT2 (cid (@weak_dual_realisation_exists R Y NY hNY D ed DN hD))). Qed.
End WeakDualRealisation.
