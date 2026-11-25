(** Opaque normed finite products supporting Federer (1969),
    3.1.1(4), p. 210. The implementation is accessible only here;
    later proofs use the specified coordinates and norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom NormedFamilyUP NormedFamilyConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type NormedFamilySignature.
(** Source for [space]: the finite product of the normed vector
    spaces in Federer 3.1.1(4), p. 210. *)
Parameter space : forall (R : realType) m, ('I_m -> lmodType R) -> lmodType R.
(** Source for [coordinate]: linear projections from the finite
    product supporting 3.1.1(4), p. 210. *)
Parameter coordinate : forall (R : realType) m (V : 'I_m -> lmodType R)
  (i : 'I_m), Hom (@space R m V) (V i).
(** Source for [norm]: a compatible sum norm on the product
    supporting 3.1.1(4), p. 210. *)
Parameter norm : forall (R : realType) m (V : 'I_m -> lmodType R),
  (forall i, V i -> R) -> @space R m V -> R.
(** Source for [laws]: the abstract product specification proved
    by the hidden implementation for 3.1.1(4), p. 210. *)
Parameter laws : forall (R : realType) m (V : 'I_m -> lmodType R)
  (N : forall i, V i -> R),
  is_normed_family N (@coordinate R m V) (@norm R m V N).
End NormedFamilySignature.
Module NormedFamily : NormedFamilySignature.
(** Source for [space]: private product witness for 3.1.1(4), p. 210. *)
Definition space (R : realType) m (V : 'I_m -> lmodType R) : lmodType R :=
  [the lmodType R of normed_family_carrier V].
(** Source for [coordinate]: private coordinate witness for
    3.1.1(4), p. 210. *)
Definition coordinate (R : realType) m (V : 'I_m -> lmodType R) i :
    Hom (@space R m V) (V i) := @normed_family_coordinate_witness R m V i.
(** Source for [norm]: private norm witness for 3.1.1(4), p. 210. *)
Definition norm (R : realType) m (V : 'I_m -> lmodType R)
    (N : forall i, V i -> R) : @space R m V -> R :=
  @normed_family_norm_witness R m V N.
(** Source for [laws]: proved laws of the selected witness,
    supporting 3.1.1(4), p. 210. *)
Lemma laws (R : realType) m (V : 'I_m -> lmodType R)
    (N : forall i, V i -> R) :
  is_normed_family N (@coordinate R m V) (@norm R m V N).
Proof. exact: normed_family_witness_laws. Qed.
End NormedFamily.
