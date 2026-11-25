(** Federer (1969), 3.1.11, pp. 219–221:
    recovering the class of a function from the
    class of its exact derivative field. This is
    the converse direction used in the inductions
    for higher composition and inversion. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearGroupingFamily NormLinearIsometryInverse
  NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialLocal NormHigherDifferentialGrouping
  NormClassHigherUP NormClassHigherDerivative NormClassZeroPostcompose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_higher_from_derivative_field]:
    the defining recursion and the D^q D^p
    identity of Federer 3.1.11, p. 219,
    show that a class-q pth differential
    yields a class-(p+q) original function.
    The supplied field is required to be the
    exact differential throughout the open domain. *)
Theorem norm_class_higher_from_derivative_field (R : realType) p q
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
    (A : X->Prop) (f : X->Y) (G : X->Z p) :
  norm_class_zero NX NY A f ->
  (forall a, A a -> has_norm_higher_differential NX ez ZN A f p a (G a)) ->
  norm_class_higher NX (@ZN p) ew WN A G q ->
  norm_class_higher NX NY ez ZN A f (p+q)%N.
Proof.
move=> hf hG [_ [D [hD hcD]]].
have hNp := continuous_multilinear_norm_is_norm hNY (@hZ p).
have hopen a (ha : A a) : norm_domain_interior NX A a := (hf a ha).1.
have hrepresent x z :
    has_norm_higher_differential NX ez ZN A f p x z -> G x=z.
  move=> hz; have hx := norm_higher_differential_domain hNX hz.
  exact (norm_higher_differential_unique hNX hNY hZ (hG x hx) hz).
pose B x := exists z, has_norm_higher_differential NX ez ZN A f p x z.
have hAB x : A x -> B x by move=> hx; exists (G x); exact: hG x hx.
have [J [K [hJ [hJN [hJK hKJ]]]]] :=
  continuous_multilinear_grouping_family_exists hNX hNY hZ hW.
have hKN z : @ZN (p+q)%N (K q z)=@WN q z by rewrite -hJN hJK.
split; first exact hf.
exists (fun x=>K q (D x)); split.
- move=> a ha.
  have hr := @norm_higher_differential_open_restriction R X (Z p) NX (@ZN p)
    hNX hNp W ew WN hW q B A G hAB hopen a ha (D a).
  have hDB : has_norm_higher_differential NX ew WN B G q a (D a).
    exact: hr.2 (hD a ha).
  have hg := @norm_higher_differential_grouping R X Y NX NY hNX
    Z ez ZN hZ p W ew WN J K hJ hJN hJK hKJ
    A f G hrepresent q a (D a).
  have [z [hz hw]] := hg.1 hDB.
  by rewrite hw hKJ.
- exact (@norm_class_zero_postcompose R X (W q) (Z (p+q)%N) NX
    (@WN q) (@ZN (p+q)%N)
    (continuous_multilinear_norm_is_norm hNp (@hW q))
    A D (K q) hcD
    (@norm_linear_isometry_bounded R (W q) (Z (p+q)%N)
      (@WN q) (@ZN (p+q)%N) (K q) hKN)).
Qed.

(** Source for [norm_class_higher_first_field_iff]:
    the successor induction used for composition
    and inverses in Federer 3.1.11,
    p. 220: class k+1 is equivalent
    to class k of the existing first differential.
    The original domain and derivative graph are unchanged. *)
Theorem norm_class_higher_first_field_iff (R : realType) k
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i))
    (W : nat->lmodType R)
    (ew : forall j, {ffun 'I_j->X}->Hom (W j) (Z 1%N))
    (WN : forall j, W j->R)
    (hW : forall j, is_continuous_multilinear_space NX (@ZN 1%N) (@ew j) (@WN j))
    (A : X->Prop) (f : X->Y) (G : X->Z 1%N) :
  norm_class_zero NX NY A f ->
  (forall a, A a -> has_norm_higher_differential NX ez ZN A f 1%N a (G a)) ->
  (norm_class_higher NX NY ez ZN A f k.+1 <->
    norm_class_higher NX (@ZN 1%N) ew WN A G k).
Proof.
move=> hf hG; rewrite -(add1n k); split.
- move=> hk.
  exact (@norm_class_higher_derivative_field R 1%N k X Y NX NY hNX hNY
    Z ez ZN hZ W ew WN hW A f G hk hG).
- move=> hk.
  exact (@norm_class_higher_from_derivative_field R 1%N k X Y NX NY hNX hNY
    Z ez ZN hZ W ew WN hW A f G hf hG hk).
Qed.
