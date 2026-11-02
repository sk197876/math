(** Federer (1969), 3.1.11, pp. 218–219:
    uniqueness and exact domains of the recursively specified
    higher differentials. Only abstract multilinear-space laws
    and the ordinary differential are used. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialLocal NormDifferentialDirectional ContinuousMultilinearUP
  ContinuousMultilinearNorm ContinuousMultilinearZero MultilinearSuccessorArguments
  NormHigherDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section HigherLaws.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).
Variable A : X->Prop.
Variable f : X->Y.
Local Notation HD := (@has_norm_higher_differential R X Y NX Z evaluation ZN A f).

(** Source for [norm_higher_differential_unique]: the notation
    D^k f(a) is single valued, as required by the recursion
    in Federer 3.1.11, pp. 218–219. Different total
    representatives of the preceding partial differential
    agree on its actual domain. *)
Theorem norm_higher_differential_unique k a (z w : Z k) :
  HD k a z -> HD k a w -> z=w.
Proof.
case: k z w=> [z w|k z w] /=.
- move=> [_ hz] [_ hw].
  apply: (continuous_multilinear_zero_injective (@hZ 0%N)).
  by rewrite hz hw.
- move=> [g [hg [L [hL heL]]]] [q [hq [M [hM heM]]]].
  have hsame x : (exists u, HD k x u) -> g x=q x.
    by move=> [u hu]; rewrite (hg x u hu) (hq x u hu).
  have hLq := norm_differential_domain_agreement hNX hsame hL.
  have hnorm := continuous_multilinear_norm_is_norm hNY (@hZ k).
  have hLM := norm_differential_unique hNX hnorm hLq hM.
  apply: (continuous_multilinear_extensional (@hZ k.+1))=> v.
  have [u [x ->]] := multilinear_successor_arguments_surjective v.
  by rewrite -heL -heM hLM.
Qed.

(** Source for [norm_higher_differential_zero_domain]: D^0 f
    has exactly the original domain, Federer 3.1.11,
    pp. 218–220. *)
Lemma norm_higher_differential_zero_domain a :
  (exists z, HD 0%N a z) <-> A a.
Proof.
split; first by move=> [z [ha _]].
move=> ha.
have [z hz] := continuous_multilinear_zero_surjective hNY (@hZ 0%N) (f a).
by exists z.
Qed.

(** Source for [norm_higher_differential_previous_domain]:
    a higher differential can exist only where the preceding
    differential is defined, Federer 3.1.11, p. 219.
    In fact its defining domain contains a neighbourhood of a. *)
Lemma norm_higher_differential_previous_domain k a (z : Z k.+1) :
  HD k.+1 a z -> exists w, HD k a w.
Proof.
move=> [g [hg [L [hL heL]]]].
exact: (@norm_domain_interior_member R X NX hNX
  (fun x=>exists w, HD k x w) a (norm_differential_interior hL)).
Qed.

(** Source for [norm_higher_differential_interior_previous]:
    the interior-domain condition implicit in D(D^k f),
    Federer 3.1.11, p. 219, refers to the exact
    preceding domain rather than all of X. *)
Lemma norm_higher_differential_interior_previous k a (z : Z k.+1) :
  HD k.+1 a z -> norm_domain_interior NX (fun x=>exists w, HD k x w) a.
Proof. by move=> [g [hg [L [hL heL]]]]; exact: norm_differential_interior hL. Qed.

(** Source for [norm_higher_differential_domain]: every
    D^k f(a) lies over a point of the original domain,
    supporting the recursive convention of Federer 3.1.11,
    pp. 218–219. *)
Lemma norm_higher_differential_domain k a (z : Z k) :
  HD k a z -> A a.
Proof.
elim: k z=> [z|k ih z] h.
- exact: h.1.
- have [w hw] := norm_higher_differential_previous_domain h.
  exact: ih w hw.
Qed.
End HigherLaws.
