(** Opaque smooth radial cutoff for Federer (1969),
    3.1.13, p. 224. Downstream proofs
    use only its plateau, range, radial
    and actual higher-differentiability laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  NormClassHigherUP NormUnitBumpUP NormUnitBumpConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type NormUnitBumpSignature.
(** Source for [value]: the radial cutoff mu,
    Federer 3.1.13, p. 224. *)
Parameter value : forall (R : realType) (X : lmodType R)
  (N : X->R) (B : X->X->R^o),
  is_real_norm N -> norm_squared_bilinear_form N B -> X->R.
(** Source for [laws]: the plateau, radial
    and range laws of mu, Federer
    3.1.13, p. 224, are proved. *)
Parameter laws : forall (R : realType) (X : lmodType R)
  (N : X->R) (B : X->X->R^o)
  (hN : is_real_norm N) (hB : norm_squared_bilinear_form N B),
  is_norm_unit_bump N (@value R X N B hN hB).
(** Source for [smooth]: actual higher smoothness
    of mu, Federer 3.1.13, p. 224,
    in any lawful abstract multilinear spaces. *)
Parameter smooth : forall (R : realType) (X : lmodType R)
  (N : X->R) (B : X->X->R^o)
  (hN : is_real_norm N) (hB : norm_squared_bilinear_form N B)
  (Z : nat->lmodType R)
  (ez : forall k, {ffun 'I_k->X}->Hom (Z k) R^o)
  (ZN : forall k, Z k->R),
  (forall k, is_continuous_multilinear_space N
    (fun t : R^o=>`|t|) (@ez k) (@ZN k)) ->
  norm_class_infinity N (fun t : R^o=>`|t|) ez ZN
    (fun _=>True) (@value R X N B hN hB).

(** Source for [profile]: the smooth scalar
    gamma in mu(x)=gamma(|x|), Federer
    3.1.13, p. 224. *)
Parameter profile : forall R : realType, R->R.
(** Source for [profile_laws]: gamma takes
    values in [0,1], is one
    on t<=1, and zero on
    t>=2, Federer 3.1.13, p. 224. *)
Parameter profile_laws : forall R : realType, is_scalar_radial_cutoff (@profile R).
(** Source for [profile_formula]: the exact
    displayed radial identity, Federer 3.1.13, p. 224. *)
Parameter profile_formula : forall (R : realType) (X : lmodType R)
  (N : X->R) (B : X->X->R^o)
  (hN : is_real_norm N) (hB : norm_squared_bilinear_form N B) x,
  @value R X N B hN hB x=@profile R (N x).
(** Source for [profile_smooth]: gamma is
    smooth on the entire scalar line,
    Federer 3.1.13, p. 224. *)
Parameter profile_smooth : forall (R : realType)
  (Z : nat->lmodType R)
  (ev : forall i, {ffun 'I_i->R^o}->Hom (Z i) R^o)
  (ZN : forall i, Z i->R),
  (forall i, is_continuous_multilinear_space (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) (@ev i) (@ZN i)) ->
  norm_class_infinity (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    ev ZN (fun _=>True) (@profile R).

End NormUnitBumpSignature.

Module NormUnitBump : NormUnitBumpSignature.
(** Source for [value]: the proved private
    witness for mu, Federer 3.1.13, p. 224. *)
Definition value (R : realType) (X : lmodType R)
    (N : X->R) (B : X->X->R^o)
    (hN : is_real_norm N) (hB : norm_squared_bilinear_form N B) : X->R :=
  @norm_unit_bump_witness R X B.
(** Source for [laws]: proof of the
    abstract cutoff laws, Federer 3.1.13, p. 224. *)
Lemma laws (R : realType) (X : lmodType R)
    (N : X->R) (B : X->X->R^o)
    (hN : is_real_norm N) (hB : norm_squared_bilinear_form N B) :
  is_norm_unit_bump N (@value R X N B hN hB).
Proof. exact: (norm_unit_bump_witness_laws hN hB). Qed.
(** Source for [smooth]: proof of all
    higher differentiability classes, Federer 3.1.13,
    p. 224. *)
Lemma smooth (R : realType) (X : lmodType R)
    (N : X->R) (B : X->X->R^o)
    (hN : is_real_norm N) (hB : norm_squared_bilinear_form N B)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) R^o)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space N
      (fun t : R^o=>`|t|) (@ez k) (@ZN k)) :
  norm_class_infinity N (fun t : R^o=>`|t|) ez ZN
    (fun _=>True) (@value R X N B hN hB).
Proof. exact: (norm_unit_bump_witness_smooth hN hB hZ). Qed.

(** Source for [profile]: the privately
    proved smooth gamma witness, Federer
    3.1.13, p. 224. *)
Definition profile (R : realType) := @norm_unit_bump_profile_witness R.
(** Source for [profile_laws]: proof of
    gamma's scalar cutoff laws, Federer
    3.1.13, p. 224. *)
Lemma profile_laws (R : realType) : is_scalar_radial_cutoff (@profile R).
Proof. exact: norm_unit_bump_profile_witness_laws. Qed.
(** Source for [profile_formula]: proof of
    mu(x)=gamma(|x|), Federer 3.1.13, p. 224. *)
Lemma profile_formula (R : realType) (X : lmodType R)
    (N : X->R) (B : X->X->R^o)
    (hN : is_real_norm N) (hB : norm_squared_bilinear_form N B) x :
  @value R X N B hN hB x=@profile R (N x).
Proof. exact: (norm_unit_bump_witness_radial_profile hN hB x). Qed.
(** Source for [profile_smooth]: proof of
    actual higher smoothness of gamma,
    Federer 3.1.13, p. 224. *)
Lemma profile_smooth (R : realType)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space (fun t : R^o=>`|t|)
      (fun t : R^o=>`|t|) (@ev i) (@ZN i)) :
  norm_class_infinity (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    ev ZN (fun _=>True) (@profile R).
Proof. exact: (norm_unit_bump_profile_witness_smooth hZ). Qed.

End NormUnitBump.
