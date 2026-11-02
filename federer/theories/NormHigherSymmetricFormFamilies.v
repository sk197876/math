(** Federer (1969), 3.1.11, pp. 219–222:
    a finite family of actual differential values
    has symmetric-form representatives with exactly the
    same finite operator norms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal.
From Federer Require Import Hom RealNormUP SymmetricForms SymmetricOperatorNorm
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferentialSymmetricForm
  NormHigherSymmetricFormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_point_forms]:
    the forms D^i f(a), with their
    corrected norms from p. 219, can
    be used in the symmetric-form products
    on Federer 3.1.11, p. 222.
    No values above the available order are
    constrained or used. *)
Theorem norm_higher_differential_point_forms (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) n a (D : forall i, Z i) :
  (forall i, (i<=n)%N -> has_norm_higher_differential NX ev ZN A f i a (D i)) ->
  exists phi : forall i, S_m X Y i, forall i, (i<=n)%N ->
    is_norm_higher_differential_form NX ev ZN A f i a (phi i) /\
    symmetric_operator_norm hNX.1 NY (phi i)=(@ZN i (D i))%:E.
Proof.
move=>hD.
have hex i : exists phi : S_m X Y i, (i<=n)%N ->
    is_norm_higher_differential_form NX ev ZN A f i a phi /\
    symmetric_operator_norm hNX.1 NY phi=(@ZN i (D i))%:E.
  case hi:(i<=n)%N.
  - have [phi [he hnorm]] := norm_higher_differential_symmetric_form_exists
      hNX hNY hZ (hD i hi).
    exists phi=>_; split; last exact hnorm.
    exists (D i); split; first exact: (hD i hi).
    move=>u; rewrite he; congr (@ev i _ (D i)).
    by apply/ffunP=>j; rewrite ffunE tnth_mktuple.
  - by exists 0.
pose phi i := projT1 (cid (hex i)).
exists phi=>i hi; exact: (projT2 (cid (hex i)) hi).
Qed.
