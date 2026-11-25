(** Private finite-product witness supporting Federer (1969),
    3.1.1(4), p. 210. Dependent finite functions establish existence
    of the abstract product; downstream proofs use the sealed laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Witness.
Variable R : realType.
Variable m : nat.
Variable V : 'I_m -> lmodType R.

(** Source for [normed_family_carrier]: private Cartesian-product
    carrier witnessing the product in 3.1.1(4), p. 210. *)
Definition normed_family_carrier : Type := {dffun forall i, V i}.
HB.instance Definition _ := Choice.copy normed_family_carrier
  {dffun forall i, V i}.
(** Source for [normed_family_zero]: componentwise zero in the
    product witness supporting 3.1.1(4), p. 210. *)
Definition normed_family_zero : normed_family_carrier := [ffun i : 'I_m => 0 : V i].
(** Source for [normed_family_add]: componentwise addition in the
    product witness supporting 3.1.1(4), p. 210. *)
Definition normed_family_add (x y : normed_family_carrier) : normed_family_carrier :=
  [ffun i : 'I_m => x i+y i].
(** Source for [normed_family_opp]: componentwise negation in the
    product witness supporting 3.1.1(4), p. 210. *)
Definition normed_family_opp (x : normed_family_carrier) : normed_family_carrier :=
  [ffun i : 'I_m => -x i].
(** Source for [normed_family_addA]: associative addition in the
    product witness supporting 3.1.1(4), p. 210. *)
Lemma normed_family_addA : associative normed_family_add.
Proof. by move=> x y z; apply/ffunP=> i; rewrite /normed_family_add !ffunE addrA. Qed.
(** Source for [normed_family_addC]: commutative addition in the
    product witness supporting 3.1.1(4), p. 210. *)
Lemma normed_family_addC : commutative normed_family_add.
Proof. by move=> x y; apply/ffunP=> i; rewrite /normed_family_add !ffunE addrC. Qed.
(** Source for [normed_family_add0]: the zero law in the product
    witness supporting 3.1.1(4), p. 210. *)
Lemma normed_family_add0 : left_id normed_family_zero normed_family_add.
Proof. by move=> x; apply/ffunP=> i; rewrite /normed_family_add /normed_family_zero !ffunE add0r. Qed.
(** Source for [normed_family_addN]: additive inverses in the
    product witness supporting 3.1.1(4), p. 210. *)
Lemma normed_family_addN : left_inverse normed_family_zero normed_family_opp normed_family_add.
Proof. by move=> x; apply/ffunP=> i; rewrite /normed_family_add /normed_family_opp /normed_family_zero !ffunE addNr. Qed.
HB.instance Definition _ := GRing.isZmodule.Build normed_family_carrier
  normed_family_addA normed_family_addC normed_family_add0 normed_family_addN.

(** Source for [normed_family_scale]: componentwise scalar action
    in the product witness supporting 3.1.1(4), p. 210. *)
Definition normed_family_scale (c : R) (x : normed_family_carrier) : normed_family_carrier :=
  [ffun i : 'I_m => c *: x i].
(** Source for [normed_family_scaleA]: associative scalar action
    in the product witness supporting 3.1.1(4), p. 210. *)
Lemma normed_family_scaleA a b x :
  normed_family_scale a (normed_family_scale b x)=normed_family_scale (a*b) x.
Proof. by apply/ffunP=> i; rewrite /normed_family_scale !ffunE scalerA. Qed.
(** Source for [normed_family_scale1]: unit scalar action in the
    product witness supporting 3.1.1(4), p. 210. *)
Lemma normed_family_scale1 : left_id 1 normed_family_scale.
Proof. by move=> x; apply/ffunP=> i; rewrite /normed_family_scale ffunE scale1r. Qed.
(** Source for [normed_family_scaleDr]: distribution over vectors
    in the product witness supporting 3.1.1(4), p. 210. *)
Lemma normed_family_scaleDr a : {morph normed_family_scale a : x y / x+y}.
Proof. by move=> x y; apply/ffunP=> i; rewrite /normed_family_scale /normed_family_add !ffunE scalerDr. Qed.
(** Source for [normed_family_scaleDl]: distribution over scalars
    in the product witness supporting 3.1.1(4), p. 210. *)
Lemma normed_family_scaleDl x : {morph normed_family_scale^~ x : a b / a+b}.
Proof. by move=> a b; apply/ffunP=> i; rewrite /normed_family_scale /normed_family_add !ffunE scalerDl. Qed.
HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R normed_family_carrier
  normed_family_scaleA normed_family_scale1 normed_family_scaleDr normed_family_scaleDl.

(** Source for [normed_family_coordinate_linear]: linearity of
    coordinate evaluation in the product witness for 3.1.1(4), p. 210. *)
Lemma normed_family_coordinate_linear i : linear (fun x : normed_family_carrier => x i).
Proof. by move=> c x y; rewrite /normed_family_add /normed_family_scale !ffunE. Qed.
(** Source for [normed_family_coordinate_witness]: coordinate maps
    of the private product witness for 3.1.1(4), p. 210. *)
Definition normed_family_coordinate_witness i : Hom [the lmodType R of normed_family_carrier] (V i) :=
  @HomMap R [the lmodType R of normed_family_carrier] (V i) (fun x : normed_family_carrier => x i) (introT (asboolP _) (normed_family_coordinate_linear i)).
(** Source for [normed_family_norm_witness]: the sum norm witness
    for the abstract product supporting 3.1.1(4), p. 210. *)
Definition normed_family_norm_witness (N : forall i, V i -> R)
    (x : normed_family_carrier) := \sum_(i<m) N i (x i).
(** Source for [normed_family_witness_laws]: existence proof of
    the specified normed product supporting 3.1.1(4), p. 210.
    The norm laws follow abstractly from the product specification. *)
Lemma normed_family_witness_laws (N : forall i, V i -> R) :
  is_normed_family N normed_family_coordinate_witness (normed_family_norm_witness N).
Proof.
constructor.
- move=> x y h; apply/ffunP=> i; exact: h.
- move=> x; exists x; by move=> i.
- by move=> x.
Qed.
End Witness.
