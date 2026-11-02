(** Federer (1969), 3.1.11, pp. 219–220:
    a rule for proving the recursive higher differential
    from fields on an open function domain. The exact
    domain is recovered from the graph laws, not assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocalAgreement
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferentialUnique
  NormHigherDifferential MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section HigherFields.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).

(** Source for [norm_higher_differential_field_domain]:
    if the kth differential exists everywhere on A,
    its exact domain is A, supporting the class-k
    definitions in Federer 3.1.11, p. 220. *)
Lemma norm_higher_differential_field_domain
    (A : X->Prop) (f : X->Y) k (D : X->Z k) :
  (forall x, A x -> has_norm_higher_differential NX evaluation ZN A f k x (D x)) ->
  forall x, (exists z, has_norm_higher_differential NX evaluation ZN A f k x z)<->A x.
Proof.
move=> hD x; split.
- move=> [z hz]; have hh := norm_higher_differential_domain hNX hz.
  exact hh.
- move=> hx; by exists (D x); exact: hD x hx.
Qed.

(** Source for [norm_higher_differential_field_step]:
    a supporting introduction rule for D^(k+1)f=D(D^k f)
    in Federer 3.1.11, p. 219. Existence of
    D^k f throughout A identifies the exact preceding
    domain, so the derivative of its representative on A
    proves the printed recursive claim without an extra hypothesis. *)
Theorem norm_higher_differential_field_step (A : X->Prop) (f : X->Y)
    k (D : X->Z k) (a : X) (L : Hom X (Z k)) (z : Z k.+1) :
  (forall x, A x -> has_norm_higher_differential NX evaluation ZN A f k x (D x)) ->
  has_norm_differential NX (@ZN k) A D a L ->
  (forall u v, @evaluation k u (L v)=
    @evaluation k.+1 (multilinear_successor_arguments u v) z) ->
  has_norm_higher_differential NX evaluation ZN A f k.+1 a z.
Proof.
move=> hD hL he.
have hdom := norm_higher_differential_field_domain hD.
have [g hg] := @norm_higher_differential_representative_exists
  R X Y NX NY hNX hNY Z evaluation ZN hZ A f k.
exists g; split; first exact hg.
exists L; split; last exact he.
apply: (@norm_differential_local_agreement R X (Z k) NX (@ZN k) hNX
  A (fun x=>exists w, has_norm_higher_differential NX evaluation ZN A f k x w)
  D g a L 1 ltr01 _ _ hL).
- move=> h _; exact: iff_sym (hdom (a+h)).
- move=> h _ hh; symmetry; exact: hg _ _ (hD _ hh).
Qed.

(** Source for [norm_higher_differential_field_previous]:
    an everywhere-defined (k+1)st differential provides
    a representative of the kth differential on the
    whole original domain, Federer 3.1.11, pp. 219–220. *)
Lemma norm_higher_differential_field_previous (A : X->Prop) (f : X->Y)
    k (D : X->Z k.+1) :
  (forall x, A x -> has_norm_higher_differential NX evaluation ZN A f k.+1 x (D x)) ->
  exists G : X->Z k, forall x, A x ->
    has_norm_higher_differential NX evaluation ZN A f k x (G x).
Proof.
move=> hD.
have [G hG] := @norm_higher_differential_representative_exists
  R X Y NX NY hNX hNY Z evaluation ZN hZ A f k.
exists G=> x hx.
have [w hw] := norm_higher_differential_previous_domain hNX (hD x hx).
by rewrite (hG x w hw).
Qed.

(** Source for [norm_higher_differential_field_step_elim]:
    the converse field rule for D^(k+1)f=D(D^k f),
    Federer 3.1.11, p. 219. When the kth
    differential is defined throughout A, its representative
    can be differentiated directly on A. *)
Lemma norm_higher_differential_field_step_elim (A : X->Prop) (f : X->Y)
    k (D : X->Z k) (a : X) (z : Z k.+1) :
  (forall x, A x -> has_norm_higher_differential NX evaluation ZN A f k x (D x)) ->
  has_norm_higher_differential NX evaluation ZN A f k.+1 a z ->
  exists L : Hom X (Z k),
    has_norm_differential NX (@ZN k) A D a L /\
    forall u v, @evaluation k u (L v)=
      @evaluation k.+1 (multilinear_successor_arguments u v) z.
Proof.
move=> hD [g [hg [L [hL he]]]].
have hdom := norm_higher_differential_field_domain hD.
exists L; split; last exact he.
apply: (@norm_differential_local_agreement R X (Z k) NX (@ZN k) hNX
  (fun x=>exists w, has_norm_higher_differential NX evaluation ZN A f k x w)
  A g D a L 1 ltr01 _ _ hL).
- move=> h _; exact: hdom (a+h).
- move=> h _ hh; apply: hg; exact: hD _ ((hdom _).1 hh).
Qed.

End HigherFields.
