(** Federer (1969), 3.1.11, pp. 218–219:
    the first higher differential is precisely the ordinary
    differential. Abstract degree-zero and degree-one value
    spaces are identified using their proved evaluation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormDifferentialIsometricEvaluation ContinuousMultilinearUP
  ContinuousMultilinearZero ContinuousMultilinearOne ContinuousMultilinearCurrying
  MultilinearArguments MultilinearSuccessorArguments
  NormHigherDifferentialUP NormHigherDifferentialUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_higher_differential_first]: the convention
    that once differentiable means differentiable, Federer
    3.1.11, p. 219, with D^1 f=Df from p. 218.
    Both directions retain the exact original domain. *)
Theorem norm_higher_differential_first (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k))
    (A : set X) (f : X->Y) (a : X) (z : Z 1%N) :
  has_norm_higher_differential NX evaluation ZN A f 1%N a z <->
  has_norm_differential NX NY A f a
    (@continuous_multilinear_one_operator R X Y (Z 1%N) NX NY
      (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N) z).
Proof.
pose E := @evaluation 0%N [ffun i : 'I_0=>(0:X)].
pose Lz := @continuous_multilinear_one_operator R X Y (Z 1%N) NX NY
  (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N) z.
have hE : forall w, @ZN 0%N w=NY (E w).
  move=> w; exact: (continuous_multilinear_zero_norm hNY (@hZ 0%N) w).
have hdom : [set x | exists w,
    has_norm_higher_differential NX evaluation ZN A f 0%N x w]=A.
  apply/seteqP; split=> x hx.
  - exact: (@norm_higher_differential_zero_domain R X Y NX NY hNY
      Z evaluation ZN hZ A f x).1 hx.
  - exact: (@norm_higher_differential_zero_domain R X Y NX NY hNY
      Z evaluation ZN hZ A f x).2 hx.
have hjoin (u : {ffun 'I_0->X}) x :
    multilinear_arguments_join u [ffun i : 'I_1=>x]=[ffun i : 'I_1=>x].
  have hh := multilinear_successor_zero_arguments u x.
  by rewrite /multilinear_successor_arguments multilinear_arguments_cast_reflexive in hh.
split.
- move=> [g [hg [L [hL heL]]]].
  have heq : hom_comp E L=Lz.
    apply: hom_ext=> v; rewrite hom_compE /E heL multilinear_successor_zero_arguments.
    by [].
  have hgf x : A x -> E (g x)=f x.
    move=> hx.
    have [w hw] : exists w, has_norm_higher_differential NX evaluation ZN A f 0%N x w.
      exact: (@norm_higher_differential_zero_domain R X Y NX NY hNY
        Z evaluation ZN hZ A f x).2 hx.
    rewrite (hg x w hw); exact: hw.2.
  have hLA : has_norm_differential NX (@ZN 0%N) A g a L.
    by rewrite -hdom.
  have hh := (@norm_differential_isometric_evaluation R X (Z 0%N) Y
    NX (@ZN 0%N) NY E hE A g a L).1 hLA.
  rewrite heq in hh.
  have hs := norm_differential_domain_agreement hNX hgf hh.
  exact hs.
- move=> hz.
  have hex x := continuous_multilinear_zero_surjective hNY (@hZ 0%N) (f x).
  have [g hg] := choice hex.
  have hf : norm_bounded_multilinear NX NY
      (fun u : {ffun 'I_1->X}=>@evaluation 1%N u z).
    split; first exact: continuous_multilinear_evaluation (@hZ 1%N) z.
    exists (@ZN 1%N z); split.
    + exact: multilinear_operator_nonnegative (continuous_multilinear_norm_laws (@hZ 1%N) z).
    + exact: multilinear_operator_bound (continuous_multilinear_norm_laws (@hZ 1%N) z).
  have [L [hL heL]] := @continuous_multilinear_curry_exists R 0 X Y (Z 0%N)
    NX NY (@evaluation 0%N) (@ZN 0%N) hNX (@hZ 0%N)
    (fun u=>@evaluation 1%N u z) hf.
  have heq : hom_comp E L=Lz.
    apply: hom_ext=> v; rewrite hom_compE /E heL hjoin; by [].
  have hfg x : A x -> f x=E (g x) by move=> _; exact: esym (hg x).
  have hd := norm_differential_domain_agreement hNX hfg hz.
  change (has_norm_differential NX NY A (fun x=>E (g x)) a Lz) in hd.
  rewrite -heq in hd.
  have hdg := (@norm_differential_isometric_evaluation R X (Z 0%N) Y
    NX (@ZN 0%N) NY E hE A g a L).2 hd.
  exists g; split.
  + move=> x w [hx hw].
    apply: (continuous_multilinear_zero_injective (@hZ 0%N)).
    by rewrite hg hw.
  + exists L; split.
    * rewrite -hdom in hdg; exact hdg.
    * move=> u v; rewrite heL hjoin multilinear_successor_zero_arguments.
      by [].
Qed.
