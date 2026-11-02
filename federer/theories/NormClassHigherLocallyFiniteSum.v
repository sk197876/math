(** Federer (1969), 3.1.13, p. 225:
    the locally finite sum of smooth functions
    is smooth, proved from its abstract finite
    evaluation laws and locality of higher differentials. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  NormClassHigherUP NormClassHigherLocal NormClassHigherLocalValues
  NormClassHigherRestriction NormClassHigherFiniteSums
  FiniteFamilySumUP NormLocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_higher_locally_finite_sum]:
    the sum u of Federer 3.1.13,
    p. 225, has each differentiability
    class shared by its summands. Every
    neighborhood sum is genuinely finite;
    no interchange with a convergent series is needed. *)
Theorem norm_class_higher_locally_finite_sum (R : realType)
    (X Y : lmodType R) (J : choiceType)
    (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@ez k) (@ZN k))
    (U : X->Prop) (I : J->Prop) (f : J->X->Y) (g : X->Y) k :
  is_norm_locally_finite_function_family NX U I f ->
  is_finite_family_sum_on U I f g ->
  (forall j, I j -> norm_class_higher NX NY ez ZN U (f j) k) ->
  norm_class_higher NX NY ez ZN U g k.
Proof.
move=> hlocal hsum hf; apply: (norm_class_higher_local hNX hNY hZ)=>a ha.
have [O [hOa [hOU [hopen [F [hFI hF]]]]]] := hlocal a ha.
exists O; split; first exact hOa; split; first exact hOU.
have hc (j : F) : norm_class_higher NX NY ez ZN O (f (val j)) k.
  apply: (norm_class_higher_open_restriction hNX hNY hZ hOU hopen).
  exact: (hf (val j) (hFI (val j) (valP j))).
have hfinite := @norm_class_higher_finite_sum R X Y NX NY hNX hNY
  Z ez ZN hZ O hopen F (fun j=>f (val j)) k hc.
apply: (@norm_class_higher_domain_agreement R X Y NX NY hNX hNY
  Z ez ZN hZ O (fun x=>\sum_(j : F) f (val j) x) g k _ hfinite).
move=>x hx; rewrite (hsum x (hOU x hx) F hFI (hF x hx)).
by rewrite big_seq_fsetE.
Qed.

(** Source for [norm_class_infinity_locally_finite_sum]:
    u is of class infinity in Federer
    3.1.13, p. 225, because
    all its locally finite summands are smooth. *)
Corollary norm_class_infinity_locally_finite_sum (R : realType)
    (X Y : lmodType R) (J : choiceType)
    (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@ez k) (@ZN k))
    (U : X->Prop) (I : J->Prop) (f : J->X->Y) (g : X->Y) :
  is_norm_locally_finite_function_family NX U I f ->
  is_finite_family_sum_on U I f g ->
  (forall j, I j -> norm_class_infinity NX NY ez ZN U (f j)) ->
  norm_class_infinity NX NY ez ZN U g.
Proof.
move=>hloc hsum hf k.
exact: (norm_class_higher_locally_finite_sum hNX hNY hZ hloc hsum (fun j hj=>hf j hj k)).
Qed.
