(** Federer (1969), 3.1.11, p. 220:
    the higher class convention agrees with class zero and
    implies all lower classes. These implications follow
    from the exact higher-differential laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormClassOneUP ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearZero NormHigherDifferentialUP NormHigherDifferentialUnique
  NormClassHigherUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ClassLaws.
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
Local Notation empty_arguments := ([ffun i : 'I_0=>(0:X)]).

(** Source for [norm_class_higher_zero]: the degree-zero
    convention agrees with the continuous-function class
    of 3.1.1, p. 210, as required by Federer 3.1.11,
    pp. 218–220. *)
Theorem norm_class_higher_zero :
  norm_class_higher NX NY evaluation ZN A f 0%N <-> norm_class_zero NX NY A f.
Proof.
split; first by move=> [hc _].
move=> hc; split; first exact hc.
have hex x := continuous_multilinear_zero_surjective hNY (@hZ 0%N) (f x).
have [D hD] := choice hex.
exists D; split.
+ by move=> a ha; split=> //.
+ move=> a ha; have [hi hb] := hc a ha.
  split=> // e he; have [d [hd hdv]] := hb e he.
  exists d; split=> // v hv hs.
  rewrite (continuous_multilinear_zero_norm hNY (@hZ 0%N)) linearB /= !hD.
  exact: hdv v hv hs.
Qed.

(** Source for [norm_class_higher_previous]: a function
  of class k+1 is of class k, Federer 3.1.11,
  p. 220. Differentiability of the kth differential
  supplies its continuity on the original open domain. *)
Theorem norm_class_higher_previous k :
norm_class_higher NX NY evaluation ZN A f k.+1 ->
norm_class_higher NX NY evaluation ZN A f k.
Proof.
move=> [hzero [D [hD hC]]].
split; first exact hzero.
have hex x : exists w : Z k, A x -> HD k x w.
case: (pselect (A x))=> [hx|hx].
- have [w hw] := @norm_higher_differential_previous_domain R X Y NX
    hNX Z evaluation ZN A f k x (D x) (hD x hx).
  by exists w.
- exists 0; by move=> h; exfalso; exact: hx h.
have [G hG] := choice hex.
exists G; split; first exact hG.
move=> a ha; split; first exact: (hC a ha).1.
move=> e he.
have [q [hq [L [hL heL]]]] := hD a ha.
have hnorm := continuous_multilinear_norm_is_norm hNY (@hZ k).
have [d [hd hb]] := norm_differential_continuous_at hnorm hL he.
exists d; split=> // v hv hs.
have hh := hb v (ex_intro _ (G (a+v)) (hG _ hv)) hs.
by rewrite (hq _ _ (hG _ hv)) (hq _ _ (hG _ ha)) in hh.
Qed.

(** Source for [norm_class_higher_lower]: all classes
  of lower degree follow from class k, as stated in
  Federer 3.1.11, p. 220. *)
Theorem norm_class_higher_lower k j :
(j<=k)%N -> norm_class_higher NX NY evaluation ZN A f k ->
norm_class_higher NX NY evaluation ZN A f j.
Proof.
elim: k j=> [j|k ih j] hj hk.
- have -> : j= 0%N by apply/eqP; rewrite eqn0Ngt -leqNgt.
exact hk.
- case: (eqVneq j k.+1)=> [->|hne]; first exact hk.
have hjk : (j<=k)%N by move: hj; rewrite leq_eqVlt (negPf hne) /= ltnS.
exact: ih j hjk (norm_class_higher_previous hk).
Qed.
End ClassLaws.
