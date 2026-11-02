(** Federer (1969), 3.1.11, p. 219:
    higher differentiation is local on the exact
    preceding domain. This allows the calculus rules
    to be proved on common open neighbourhoods. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocalAgreement
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section LocalHigherDifferentials.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).

(** Source for [norm_higher_differential_successor_local]:
    a supporting induction step for the local recursion
    D^(k+1)f=D(D^k f), Federer 3.1.11, p. 219.
    Equality of preceding graphs is required only near a. *)
Lemma norm_higher_differential_successor_local k
    (A B : X->Prop) (f g : X->Y) (a : X) (r : R) (z : Z k.+1) :
  0<r ->
  (forall h w, NX h<r ->
    (has_norm_higher_differential NX evaluation ZN A f k (a+h) w <->
     has_norm_higher_differential NX evaluation ZN B g k (a+h) w)) ->
  has_norm_higher_differential NX evaluation ZN A f k.+1 a z ->
  has_norm_higher_differential NX evaluation ZN B g k.+1 a z.
Proof.
move=> hr hlocal [p [hp [L [hL hLe]]]].
have [q hq] := @norm_higher_differential_representative_exists
  R X Y NX NY hNX hNY Z evaluation ZN hZ B g k.
exists q; split; first exact hq.
exists L; split; last exact hLe.
apply: (@norm_differential_local_agreement R X (Z k) NX (@ZN k) hNX
  (fun x=>exists w, has_norm_higher_differential NX evaluation ZN A f k x w)
  (fun x=>exists w, has_norm_higher_differential NX evaluation ZN B g k x w)
  p q a L r hr _ _ hL).
- move=> h hh; split=> [[w hw]|[w hw]]; exists w.
  + exact: (hlocal h w hh).1 hw.
  + exact: (hlocal h w hh).2 hw.
- move=> h hh [w hw].
  rewrite (hp _ _ hw); symmetry; apply: hq.
  exact: (hlocal h w hh).1 hw.
Qed.

(** Source for [norm_higher_differential_local_agreement]:
    changing a function or its domain away from an
    open neighbourhood leaves every existing higher differential
    unchanged, supporting Federer 3.1.11, p. 219.
    Both implications refer to the exact recursive domains. *)
Theorem norm_higher_differential_local_agreement k
    (A B O : X->Prop) (f g : X->Y) :
  (forall x, O x -> norm_domain_interior NX O x) ->
  (forall x, O x -> (A x<->B x)) ->
  (forall x, O x -> A x -> f x=g x) ->
  forall a, O a -> forall z : Z k,
  (has_norm_higher_differential NX evaluation ZN A f k a z <->
   has_norm_higher_differential NX evaluation ZN B g k a z).
Proof.
move=> hopen hAB hfg.
elim: k=> [|k ih] a ha z.
- split=> [[hAa he]|[hBa he]].
  + split; first exact: (hAB a ha).1 hAa.
    by rewrite -hfg.
  + have hAa := (hAB a ha).2 hBa.
    split; first exact hAa; by rewrite hfg.
- have [r [hr hO]] := hopen a ha.
  split=> hz.
  + apply: (norm_higher_differential_successor_local hr _ hz).
    move=> h w hh; exact: ih (a+h) (hO h hh) w.
  + apply: (norm_higher_differential_successor_local hr _ hz).
    move=> h w hh; exact: iff_sym (ih (a+h) (hO h hh) w).
Qed.

(** Source for [norm_higher_differential_open_restriction]:
    higher differentials of an open restriction agree
    with the original ones, a supporting domain law
    for Federer 3.1.11, p. 219. *)
Corollary norm_higher_differential_open_restriction k
    (A O : X->Prop) (f : X->Y) :
  (forall x, O x -> A x) ->
  (forall x, O x -> norm_domain_interior NX O x) ->
  forall a, O a -> forall z : Z k,
  (has_norm_higher_differential NX evaluation ZN A f k a z <->
   has_norm_higher_differential NX evaluation ZN O f k a z).
Proof.
move=> hOA hopen.
apply: norm_higher_differential_local_agreement hopen _ _.
- move=> x hx; split=> _; [exact hx|exact: hOA x hx].
- by move=> x hx hAx.
Qed.
End LocalHigherDifferentials.
