(** Federer (1969), 3.1.13, p. 224:
    translated and scaled radial cutoffs, before
    normalization by their locally finite sum.
    At radius r=5h(s) these are the
    functions u_s in the printed proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearNorm
  NormHigherDifferentialUP NormClassHigherUP NormUnitBumpUP
  NormAffineDilationDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_scaled_unit_bump]:
    u_s(x)=mu((x-s)/(5h(s))), Federer
    3.1.13, p. 224, with
    the positive scaling radius written as r. *)
Definition norm_scaled_unit_bump (R : realType) (X : lmodType R)
    (mu : X->R) (s : X) (r : R) (x : X) :=
  mu (r^-1*:(x-s)).

Section ScaledBump.
Variable R : realType.
Variable X : lmodType R.
Variable N : X->R.
Hypothesis hN : is_real_norm N.
Variable mu : X->R.
Hypothesis hmu : is_norm_unit_bump N mu.
Variable s : X.
Variable r : R.
Hypothesis hr : 0<r.

(** Source for [norm_scaled_unit_bump_range]:
    the rescaled cutoff takes values in
    [0,1], Federer 3.1.13, p. 224. *)
Lemma norm_scaled_unit_bump_range x : 0<=norm_scaled_unit_bump mu s r x<=1.
Proof. exact: (norm_unit_bump_range hmu). Qed.

(** Source for [norm_scaled_unit_bump_inner]:
    u_s is one on the closed ball
    of radius 5h(s), Federer 3.1.13,
    p. 224. *)
Lemma norm_scaled_unit_bump_inner x :
  N (x-s)<=r -> norm_scaled_unit_bump mu s r x= 1.
Proof.
move=>hx; apply: (norm_unit_bump_inner hmu).
rewrite (real_seminorm_scale hN.1) normfV (ger0_norm (ltW hr)) mulrC.
by rewrite ler_pdivrMr // mul1r.
Qed.

(** Source for [norm_scaled_unit_bump_outer]:
    u_s is zero at distance at least
    10h(s), Federer 3.1.13, p. 224.
    In particular the sphere itself has value zero. *)
Lemma norm_scaled_unit_bump_outer x :
  2*r<=N (x-s) -> norm_scaled_unit_bump mu s r x=0.
Proof.
move=>hx; apply: (norm_unit_bump_outer hmu).
rewrite (real_seminorm_scale hN.1) normfV (ger0_norm (ltW hr)) mulrC.
by rewrite ler_pdivlMr.
Qed.

Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) R^o.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N
  (fun t : R^o=>`|t|) (@ev i) (@ZN i).

(** Source for [norm_scaled_unit_bump_smooth]:
    each u_s is of class infinity on
    the whole Euclidean space, Federer
    3.1.13, p. 224. Smoothness
    follows from the actual affine-dilation calculus. *)
Theorem norm_scaled_unit_bump_smooth :
  norm_class_infinity N (fun t : R^o=>`|t|) ev ZN (fun _=>True) mu ->
  norm_class_infinity N (fun t : R^o=>`|t|) ev ZN
    (fun _=>True) (norm_scaled_unit_bump mu s r).
Proof.
move=>hc; have hd := @norm_class_infinity_affine_dilation R X R^o N
  (fun t : R^o=>`|t|) hN (@scalar_absolute_value_norm R) Z ev ZN hZ
  mu r^-1 (- (r^-1*:s)) hc.
have he : (fun x=>mu (r^-1*:x+ -(r^-1*:s)))=norm_scaled_unit_bump mu s r.
  apply: funext=>x; by rewrite /norm_scaled_unit_bump scalerBr.
by rewrite he in hd.
Qed.

(** Source for [norm_scaled_unit_bump_differential]:
    D^i u_s(x)=(5h(s))^(-i)
    D^i mu((x-s)/(5h(s))),
    Federer 3.1.13, p. 224. *)
Theorem norm_scaled_unit_bump_differential k (D : X->Z k) :
  (forall x, has_norm_higher_differential N ev ZN (fun _=>True) mu k x (D x)) ->
  forall x, has_norm_higher_differential N ev ZN (fun _=>True)
    (norm_scaled_unit_bump mu s r) k x
    ((r^-1)^+k*:D (r^-1*:(x-s))).
Proof.
move=>hD x.
have hd := @norm_higher_differential_affine_dilation R X R^o N
  (fun t : R^o=>`|t|) hN (@scalar_absolute_value_norm R) Z ev ZN hZ
  mu r^-1 (- (r^-1*:s)) k D hD x.
have he : (fun x=>mu (r^-1*:x+ -(r^-1*:s)))=norm_scaled_unit_bump mu s r.
  apply: funext=>y; by rewrite /norm_scaled_unit_bump scalerBr.
by rewrite he -scalerBr in hd.
Qed.

(** Source for [norm_scaled_unit_bump_differential_bound]:
    the derivative bound G_i/(5h(s))^i
    for u_s, Federer 3.1.13,
    p. 224, retaining the printed
    scaling constant five. *)
Theorem norm_scaled_unit_bump_differential_bound k (D : X->Z k) G :
  (forall x, @ZN k (D x)<=G) ->
  forall x, @ZN k ((r^-1)^+k*:D (r^-1*:(x-s)))<=G/r^+k.
Proof.
move=>hD x.
have hNk := continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R) (@hZ k).
have hinv : 0<r^-1 by rewrite invr_gt0.
rewrite (real_seminorm_scale hNk.1) normrX (ger0_norm (ltW hinv)).
have hh := ler_wpM2l (exprn_ge0 k (ltW hinv)) (hD (r^-1*:(x-s))).
rewrite exprVn mulrC in hh.
by rewrite exprVn mulrC [X in _<=X]mulrC.
Qed.
End ScaledBump.
