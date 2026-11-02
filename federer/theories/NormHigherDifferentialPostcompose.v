(** Federer (1969), 3.1.11, pp. 219–220:
    every higher differential commutes with a
    bounded linear operation on the target.
    The proof uses exact derivative fields on
    the original domain and abstract multilinear lifts. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferentialFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_field_postcompose]:
    the linear special case of the higher
    chain rule in Federer 3.1.11,
    p. 220. The target lift is
    specified only by evaluation and a bound;
    no construction of multilinear spaces is used. *)
Theorem norm_higher_differential_field_postcompose (R : realType)
    (X U V : lmodType R) (NX : X->R) (NU : U->R) (NV : V->R)
    (hNX : is_real_norm NX) (hNU : is_real_norm NU) (hNV : is_real_norm NV)
    (P Q : nat->lmodType R)
    (ep : forall k, {ffun 'I_k->X}->Hom (P k) U) (PN : forall k, P k->R)
    (eq : forall k, {ffun 'I_k->X}->Hom (Q k) V) (QN : forall k, Q k->R)
    (hP : forall k, is_continuous_multilinear_space NX NU (@ep k) (@PN k))
    (hQ : forall k, is_continuous_multilinear_space NX NV (@eq k) (@QN k))
    (M : Hom U V) (K : forall k, Hom (P k) (Q k)) :
  (forall k z u, @eq k u (K k z)=M (@ep k u z)) ->
  (forall k, norm_bounded_linear (@PN k) (@QN k) (K k)) ->
  forall (A : X->Prop) (f : X->U) k (D : X->P k),
    (forall x, A x -> has_norm_higher_differential NX ep PN A f k x (D x)) ->
    forall x, A x ->
      has_norm_higher_differential NX eq QN A (fun t=>M (f t))
        k x (K k (D x)).
Proof.
move=> hK hKb A f k.
elim: k=>[|k ih] D hD a ha.
- split; first exact ha.
  by rewrite hK (hD a ha).2.
- have [G hG] := norm_higher_differential_field_previous hNX hNU hP hD.
  have htarget := ih G hG.
  have [L [hL hLe]] := norm_higher_differential_field_step_elim hNX hG (hD a ha).
  have hp := norm_differential_postcompose hNX hL (hKb k).
  apply: (norm_higher_differential_field_step hNX hNV hQ htarget hp).
  by move=> u v; rewrite hom_compE hK hLe hK.
Qed.
