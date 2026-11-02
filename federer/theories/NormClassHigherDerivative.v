(** Federer (1969), 3.1.11, p. 221:
    the pth differential of a class-(p+q)
    function is of class q, under the
    canonical grouping of multilinear arguments. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearGroupingFamily NormLinearIsometryInverse
  NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferentialLocal NormHigherDifferentialGrouping
  NormClassHigherUP NormClassHigherLaws NormClassZeroPostcompose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_domain_agreement]:
    continuity depends only on values in the
    original open domain, supporting the representative
    conventions for D^p f in Federer 3.1.11,
    pp. 219–221. *)
Lemma norm_class_zero_domain_agreement (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (A : X->Prop) (f g : X->Y) :
  (forall x, A x -> f x=g x) ->
  norm_class_zero NX NY A f -> norm_class_zero NX NY A g.
Proof.
move=> he hf a ha; split; first exact: (hf a ha).1.
move=> e heps; have [d [hd hb]] := (hf a ha).2 e heps.
exists d; split=> // h hh hs.
rewrite -(he _ hh) -(he _ ha); exact: hb h hh hs.
Qed.

(** Source for [norm_class_higher_derivative_field]:
    Federer 3.1.11, p. 221: D^p f
    is of class q when f is of class
    p+q. The supplied field G must be the
    actual pth differential on A; all derivatives
    and their continuity are proved from this
    hypothesis and the original class assumption. *)
Theorem norm_class_higher_derivative_field (R : realType) p q
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
  norm_class_higher NX NY ez ZN A f (p+q)%N ->
  (forall a, A a -> has_norm_higher_differential NX ez ZN A f p a (G a)) ->
  norm_class_higher NX (@ZN p) ew WN A G q.
Proof.
move=> hk hG.
have hNp := continuous_multilinear_norm_is_norm hNY (@hZ p).
have hopen a (ha : A a) : norm_domain_interior NX A a := (hk.1 a ha).1.
have hple : (p<=p+q)%N by rewrite leq_addr.
have [_ [Gp [hGp hcGp]]] := @norm_class_higher_lower R X Y NX NY
  hNX hNY Z ez ZN hZ A f (p+q)%N p hple hk.
have hge x (hx : A x) : Gp x=G x.
  exact (norm_higher_differential_unique hNX hNY hZ (hGp x hx) (hG x hx)).
have hcG := norm_class_zero_domain_agreement hge hcGp.
have hrepresent x z :
    has_norm_higher_differential NX ez ZN A f p x z -> G x=z.
  move=> hz; have hx := norm_higher_differential_domain hNX hz.
  exact (norm_higher_differential_unique hNX hNY hZ (hG x hx) hz).
pose B x := exists z, has_norm_higher_differential NX ez ZN A f p x z.
have hAB x : A x -> B x by move=> hx; exists (G x); exact: hG x hx.
have [J [K [hJ [hJN [hJK hKJ]]]]] :=
  continuous_multilinear_grouping_family_exists hNX hNY hZ hW.
have [_ [D [hD hcD]]] := hk.
split; first exact hcG.
exists (fun x=>J q (D x)); split.
- move=> a ha.
  have hg := @norm_higher_differential_grouping R X Y NX NY hNX
    Z ez ZN hZ p W ew WN J K hJ hJN hJK hKJ
    A f G hrepresent q a (J q (D a)).
  have hw : has_norm_higher_differential NX ew WN B G q a (J q (D a)).
    apply: hg.2; exists (D a); split=> //; exact: hD a ha.
  have hr := @norm_higher_differential_open_restriction R X (Z p) NX (@ZN p)
    hNX hNp W ew WN hW q B A G hAB hopen a ha (J q (D a)).
  exact: hr.1 hw.
- exact (@norm_class_zero_postcompose R X (Z (p+q)%N) (W q) NX
    (@ZN (p+q)%N) (@WN q)
    (continuous_multilinear_norm_is_norm hNY (@hZ (p+q)%N))
    A D (J q) hcD
    (@norm_linear_isometry_bounded R (Z (p+q)%N) (W q)
      (@ZN (p+q)%N) (@WN q) (J q) (hJN q))).
Qed.
