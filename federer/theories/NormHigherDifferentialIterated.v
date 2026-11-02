(** Federer (1969), 3.1.11, p. 219:
    the iterated higher differential D^q D^p
    evaluated on the final q arguments, then
    on the first p arguments, equals D^(p+q).
    The identities use only abstract space specifications. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP
  ContinuousMultilinearGroupingFamily MultilinearArguments
  NormHigherDifferentialUP NormHigherDifferentialGrouping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_higher_differential_iterated]:
    Federer 3.1.11, p. 219, the
    displayed grouping identity verified there by
    induction on q. In both directions
    the qth differential of the actual pth
    differential has exactly the grouped evaluations
    of the (p+q)th differential of f.
    No global class assumption or additional
    regularity hypothesis is introduced. *)
Theorem norm_higher_differential_iterated (R : realType) p q
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i))
    (W : nat->lmodType R)
    (ew : forall j, {ffun 'I_j->X}->Hom (W j) (Z p))
    (WN : forall j, W j->R)
    (hW : forall j, is_continuous_multilinear_space NX (@ZN p) (@ew j) (@WN j))
    (A : X->Prop) (f : X->Y) (G : X->Z p) a (z : Z (p+q)%N) :
  (forall x v, has_norm_higher_differential NX ez ZN A f p x v -> G x=v) ->
  (has_norm_higher_differential NX ez ZN A f (p+q)%N a z <->
    exists w : W q,
      has_norm_higher_differential NX ew WN
        (fun x=>exists v, has_norm_higher_differential NX ez ZN A f p x v)
        G q a w /\
      forall u v, @ez p u (@ew q v w)=
        @ez (p+q)%N (multilinear_arguments_join u v) z).
Proof.
move=> hG.
have [J [K [hJ [hJN [hJK hKJ]]]]] :=
  continuous_multilinear_grouping_family_exists hNX hNY hZ hW.
have he := @norm_higher_differential_grouping R X Y NX NY hNX
  Z ez ZN hZ p W ew WN J K hJ hJN hJK hKJ A f G hG q a.
split.
- move=> hz; exists (J q z); split; last exact: hJ q z.
  apply: (he (J q z)).2; by exists z.
- move=> [w [hw hvalues]].
  have [z' [hz' hzw]] := (he w).1 hw.
  have hzz : z'=z.
    apply: (continuous_multilinear_extensional (@hZ (p+q)%N))=>u.
    have hh := hvalues (multilinear_arguments_left u) (multilinear_arguments_right u).
    by rewrite hzw hJ !multilinear_arguments_join_split in hh.
  by rewrite -hzz.
Qed.
