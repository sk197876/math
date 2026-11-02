(** Federer (1969), 3.1.11, p. 220:
    bounded linear target maps preserve every class k.
    This supporting result precedes the general higher
    chain rule and uses only the abstract multilinear laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearPostcompose
  NormHigherDifferentialPostcompose NormClassHigherUP NormClassZeroPostcompose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_higher_postcompose]:
    the bounded linear special case of composition
    preserving class k in Federer 3.1.11,
    p. 220. The degree-k field is
    lifted through the proved universal-property map. *)
Theorem norm_class_higher_postcompose (R : realType)
    (X U V : lmodType R) (NX : X->R) (NU : U->R) (NV : V->R)
    (hNX : is_real_norm NX) (hNU : is_real_norm NU) (hNV : is_real_norm NV)
    (P Q : nat->lmodType R)
    (ep : forall k, {ffun 'I_k->X}->Hom (P k) U) (PN : forall k, P k->R)
    (eq : forall k, {ffun 'I_k->X}->Hom (Q k) V) (QN : forall k, Q k->R)
    (hP : forall k, is_continuous_multilinear_space NX NU (@ep k) (@PN k))
    (hQ : forall k, is_continuous_multilinear_space NX NV (@eq k) (@QN k))
    (A : X->Prop) (f : X->U) (M : Hom U V) k :
  norm_bounded_linear NU NV M ->
  norm_class_higher NX NU ep PN A f k ->
  norm_class_higher NX NV eq QN A (fun x=>M (f x)) k.
Proof.
move=> hM [hf [D [hD hcD]]].
have [K [hK hKb]] := continuous_multilinear_postcompose_family_exists hP hQ hM.
split; first exact (norm_class_zero_postcompose hNU hf hM).
exists (fun x=>K k (D x)); split.
- exact (norm_higher_differential_field_postcompose hNX hNU hNV hP hQ hK hKb hD).
- exact (norm_class_zero_postcompose
    (continuous_multilinear_norm_is_norm hNU (@hP k)) hcD (hKb k)).
Qed.

(** Source for [norm_class_higher_space_independent]:
    the abstract realization of the multilinear
    spaces does not change class k,
    supporting the intrinsic interpretation of
    Federer 3.1.11, pp. 219–220.
    This prevents later arguments from depending
    on a particular construction of those spaces. *)
Theorem norm_class_higher_space_independent (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (P Q : nat->lmodType R)
    (ep : forall k, {ffun 'I_k->X}->Hom (P k) Y) (PN : forall k, P k->R)
    (eq : forall k, {ffun 'I_k->X}->Hom (Q k) Y) (QN : forall k, Q k->R)
    (hP : forall k, is_continuous_multilinear_space NX NY (@ep k) (@PN k))
    (hQ : forall k, is_continuous_multilinear_space NX NY (@eq k) (@QN k))
    (A : X->Prop) (f : X->Y) k :
  norm_class_higher NX NY ep PN A f k <->
  norm_class_higher NX NY eq QN A f k.
Proof.
have hid : linear (fun y : Y=>y) by move=> c x y.
pose Id := @HomMap R Y Y (fun y=>y) (introT (asboolP _) hid).
have hId : norm_bounded_linear NY NY Id.
  exists 1; split; first exact: ler01; by move=> y; rewrite mul1r.
split.
- move=> hk; exact (@norm_class_higher_postcompose R X Y Y NX NY NY
    hNX hNY hNY P Q ep PN eq QN hP hQ A f Id k hId hk).
- move=> hk; exact (@norm_class_higher_postcompose R X Y Y NX NY NY
    hNX hNY hNY Q P eq QN ep PN hQ hP A f Id k hId hk).
Qed.
