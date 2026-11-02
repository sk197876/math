(** Federer (1969), 3.1.11, pp. 220–222:
    the actual higher differential, viewed as a
    symmetric form in the Chapter 1 interface.
    Its graph and evaluation laws specify the object. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SymmetricForms ContinuousMultilinearUP
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialSymmetricForm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_norm_higher_differential_form]:
    D^i f(a) as a symmetric i-form,
    Federer 3.1.11, pp. 220–222.
    A witness must satisfy the exact
    recursive differential graph and all evaluations. *)
Definition is_norm_higher_differential_form (R : realType)
    (X Y : lmodType R) (NX : X->R)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R) (A : X->Prop) (f : X->Y)
    i a (phi : S_m X Y i) :=
  exists z : Z i, has_norm_higher_differential NX ev ZN A f i a z /\
    forall u, @ev i u z=phi [tuple u j | j<i].

Arguments is_norm_higher_differential_form {R X Y} NX {Z} ev ZN A f i a phi.

(** Source for [symmetric_form_finite_family_extensional]:
    the finite-family and tuple descriptions
    determine the same symmetric form, supporting
    the formulas in Federer 3.1.11,
    p. 222. *)
Lemma symmetric_form_finite_family_extensional (K : fieldType)
    (X Y : lmodType K) i (phi psi : S_m X Y i) :
  (forall u : {ffun 'I_i->X}, phi [tuple u j | j<i]=psi [tuple u j | j<i]) ->
  phi=psi.
Proof.
move=>he; apply: sform_ext=>t.
have hh := he [ffun j=>tnth t j].
have ht : [tuple [ffun j=>tnth t j] l | l<i]=t.
  by apply: eq_from_tnth=>j; rewrite tnth_mktuple ffunE.
by rewrite ht in hh.
Qed.

(** Source for [norm_higher_differential_form_unique]:
    the Chapter 1 symmetric-form representative
    of an actual differential is unique,
    Federer 3.1.11, pp. 220–222. *)
Lemma norm_higher_differential_form_unique (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) i a (phi psi : S_m X Y i) :
  is_norm_higher_differential_form NX ev ZN A f i a phi ->
  is_norm_higher_differential_form NX ev ZN A f i a psi -> phi=psi.
Proof.
move=>[z [hz hez]] [w [hw hew]].
have he := norm_higher_differential_unique hNX hNY hZ hz hw.
apply: symmetric_form_finite_family_extensional=>u; by rewrite -hez -hew he.
Qed.

(** Source for [norm_higher_differential_form_exists]:
    symmetry of D^i f(a) gives
    its Chapter 1 form representative,
    Federer 3.1.11, p. 220.
    This is a proved existence statement. *)
Lemma norm_higher_differential_form_exists (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) i a (z : Z i) :
  has_norm_higher_differential NX ev ZN A f i a z ->
  exists phi, is_norm_higher_differential_form NX ev ZN A f i a phi.
Proof.
move=>hz.
have [phi [he _]] := norm_higher_differential_symmetric_form_exists hNX hNY hZ hz.
exists phi, z; split; first exact hz.
move=>u; rewrite he.
congr (@ev i _ z); by apply/ffunP=>j; rewrite ffunE tnth_mktuple.
Qed.
