(** Federer (1969), 4.1.1, p. 346: translations
    commute with all smooth derivatives on the
    whole source. This supporting calculus identity
    reuses the field recursion of 3.1.11,
    pp. 218–219, and the existing change of origins. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP NormHigherDifferentialUP
  NormHigherDifferentialFields NormClassOneNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_higher_global_translation]: every actual
    higher differential of f(x+c) is the corresponding
    differential of f at x+c, supporting the
    Taylor difference quotients in Federer 4.1.1,
    p. 346. *)
Theorem norm_higher_global_translation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall k,{ffun 'I_k->X}->Hom (Z k) Y)
    (ZN:forall k,Z k->R) (hZ:forall k,is_continuous_multilinear_space NX NY (@ev k) (@ZN k))
    (f:X->Y) (D:forall k,X->Z k):
  (forall k x,has_norm_higher_differential NX ev ZN setT f k x (D k x)) ->
  forall c k a,has_norm_higher_differential NX ev ZN setT (fun x=>f (x+c)) k a (D k (a+c)).
Proof.
move=>hD c; elim=>[|k ih] a.
- split; first exact Logic.I; exact:(hD 0%N (a+c)).2.
- have [L [hL he]]:=@norm_higher_differential_field_step_elim R X Y NX hNX Z ev ZN
    setT f k (@D k) (a+c) (D k.+1 (a+c)) (fun x _=>hD k x) (hD k.+1 (a+c)).
  have hAt:has_norm_differential NX (@ZN k) setT (@D k) (c+a) L by rewrite addrC.
  have hTranslate:=@norm_differential_translate R X (Z k) NX (@ZN k) setT (@D k) c a 0 L hAt.
  have hFunction:(fun x=>D k (c+x)-0)=(fun x=>D k (x+c)).
    apply:funext=>x; by rewrite subr0 addrC.
  rewrite hFunction in hTranslate.
  exact:(@norm_higher_differential_field_step R X Y NX NY hNX hNY Z ev ZN hZ
    setT (fun x=>f (x+c)) k (fun x=>D k (x+c)) a L (D k.+1 (a+c))
    (fun x _=>ih x) hTranslate he).
Qed.
