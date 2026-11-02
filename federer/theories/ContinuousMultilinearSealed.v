(** Opaque continuous multilinear-map space for Federer
    (1969), 3.1.11, p. 219. Only the abstract
    evaluation and norm laws are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type ContinuousMultilinearSignature.
(** Source for [space]: the space of continuous k-linear
    maps in Federer 3.1.11, p. 219, with no
    symmetry, completeness or finite-dimensionality assumption. *)
Parameter space : forall (R : realType) (k : nat) (X Y : lmodType R)
  (NX : X->R) (NY : Y->R), is_real_norm NX -> is_real_norm NY -> lmodType R.
(** Source for [evaluation]: linear evaluation at an argument
    tuple in the multilinear space of Federer 3.1.11, p. 219. *)
Parameter evaluation : forall (R : realType) (k : nat) (X Y : lmodType R)
  (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY),
  {ffun 'I_k->X}->Hom (@space R k X Y NX NY hNX hNY) Y.
(** Source for [norm]: the corrected supremum norm in
    Federer 3.1.11, p. 219; erratum p. 4,
    book p. 219 line 4. *)
Parameter norm : forall (R : realType) (k : nat) (X Y : lmodType R)
  (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY),
  @space R k X Y NX NY hNX hNY->R.
(** Source for [laws]: exact abstract specification of the
    space and norm in Federer 3.1.11, p. 219. *)
Parameter laws : forall (R : realType) (k : nat) (X Y : lmodType R)
  (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY),
  is_continuous_multilinear_space NX NY
    (@evaluation R k X Y NX NY hNX hNY) (@norm R k X Y NX NY hNX hNY).
End ContinuousMultilinearSignature.

Module ContinuousMultilinear : ContinuousMultilinearSignature.
(** Source for [space]: hidden proved carrier for the
    multilinear-map space of Federer 3.1.11, p. 219. *)
Definition space (R : realType) (k : nat) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY) :
    lmodType R := @continuous_multilinear_carrier R k X Y NX NY hNY.
(** Source for [evaluation]: hidden evaluation witness for
    the space in Federer 3.1.11, p. 219. *)
Definition evaluation (R : realType) (k : nat) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY) :
    {ffun 'I_k->X}->Hom (@space R k X Y NX NY hNX hNY) Y :=
  @continuous_multilinear_evaluation_witness R k X Y NX NY hNY.
(** Source for [norm]: hidden finite norm witness for
    Federer 3.1.11, p. 219, with the target norm
    corrected as in erratum p. 4, book line 4. *)
Definition norm (R : realType) (k : nat) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY) :
    @space R k X Y NX NY hNX hNY->R :=
  @continuous_multilinear_norm_witness R k X Y NX NY hNX hNY.
(** Source for [laws]: the private witness proves every
    public promise for Federer 3.1.11, p. 219. *)
Lemma laws (R : realType) (k : nat) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY) :
  is_continuous_multilinear_space NX NY
    (@evaluation R k X Y NX NY hNX hNY) (@norm R k X Y NX NY hNX hNY).
Proof. exact: continuous_multilinear_witness_laws. Qed.
End ContinuousMultilinear.
