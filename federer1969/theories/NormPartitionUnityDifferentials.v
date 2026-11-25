(** Federer (1969), 3.1.13, p. 225:
    the higher differentials of a locally finite
    smooth partition remain locally finite, and their
    sum is zero in every positive degree. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  ContinuousMultilinearZero NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialSupport NormHigherDifferentialConstant NormLocalFiniteSumDifferentials
  NormLocallyFiniteFamilyUP FiniteFamilySumUP NormPartitionUnityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_locally_finite_differential_family]:
    the local finite expression for sums of
    D^i v_s in Federer 3.1.13,
    p. 225. Derivatives of a
    summand vanish wherever that summand is
    identically zero on an open neighbourhood. *)
Theorem norm_locally_finite_differential_family (R : realType)
    (X Y : lmodType R) (J : choiceType)
    (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (U : X->Prop) (I : J->Prop) (f : J->X->Y) k (D : J->X->Z k) :
  is_norm_locally_finite_function_family NX U I f ->
  (forall j, I j -> forall x, has_norm_higher_differential NX ev ZN
    (fun _=>True) (f j) k x (D j x)) ->
  is_norm_locally_finite_function_family NX U I D.
Proof.
move=>hlocal hD x hx.
have [O [hOx [hOU [hOo [F [hFI hF]]]]]] := hlocal x hx.
exists O; split; first exact hOx; split; first exact hOU; split; first exact hOo.
exists F; split; first exact hFI.
move=>y hy j hj hn.
have hzero := @norm_higher_differential_locally_zero R X Y NX NY hNX hNY
  Z ev ZN hZ O (f j) k y hOo (fun z hz=>hF z hz j hj hn) hy.
exact: (norm_higher_differential_unique hNX hNY hZ (hD j hj y) hzero).
Qed.

(** Source for [norm_partition_positive_differentials_sum_zero]:
    sum_s D^i v_s(x)=0 for i>0,
    Federer 3.1.13, p. 225.
    The sum is specified independently of any
    particular finite selection of active derivatives. *)
Theorem norm_partition_positive_differentials_sum_zero (R : realType)
    (X : lmodType R) (J : choiceType)
    (NX : X->R) (hNX : is_real_norm NX)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (U : X->Prop) (I : J->Prop) (v : J->X->R) k
    (D : J->X->Z k.+1) :
  is_norm_smooth_partition_of_unity NX ev ZN U I v ->
  (forall j, I j -> forall x, has_norm_higher_differential NX ev ZN
    (fun _=>True) (v j) k.+1 x (D j x)) ->
  is_finite_family_sum_on U I D (fun _=>0).
Proof.
move=>hp hD x hx F hFI hF.
have hlocal := norm_partition_locally_finite hp.
have [O [hOx [hOU [hOo [G [hGI hG]]]]]] := hlocal x hx.
have hDG j (hj : I j) (hn : j \notin G) : D j x=0.
  have hz := @norm_higher_differential_locally_zero R X R^o NX
    (fun t : R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
    Z ev ZN hZ O (v j) k.+1 x hOo (fun y hy=>hG y hy j hj hn) hOx.
  exact: (norm_higher_differential_unique hNX (@scalar_absolute_value_norm R) hZ
    (hD j hj x) hz).
have hsum := @norm_local_finite_sum_differential R X R^o J NX
  (fun t : R^o=>`|t|) hNX (@scalar_absolute_value_norm R) Z ev ZN hZ
  U O I v (fun _=>1) G k.+1 D
  (norm_partition_sum_one hp) hGI hOU hOo hG hD x hOx.
have hU y (hy : U y) : norm_domain_interior NX U y.
  have [V [hVy [hVU [hVo _]]]] := hlocal y hy.
  have [r [hr hball]] := hVo y hVy.
  exists r; split; first exact hr.
  move=>a ha; exact: (hVU (y+a) (hball a ha)).
have [c0 hc0] := continuous_multilinear_zero_surjective
  (@scalar_absolute_value_norm R) (@hZ 0%N) 1.
have hconst := @norm_higher_differential_constant R X R^o NX
  (fun t : R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
  Z ev ZN hZ U hU 1 c0 hc0 k.+1 x hx.
have he : (\sum_(j<-G) D j x)=0.
  exact: (norm_higher_differential_unique hNX (@scalar_absolute_value_norm R) hZ hsum hconst).
rewrite -[X in X=_]he.
exact: (finite_family_sum_selection_independent hGI hFI hDG hF).
Qed.
