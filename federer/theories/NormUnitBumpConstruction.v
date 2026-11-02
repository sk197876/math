(** Private smooth radial cutoff witness for Federer (1969),
    3.1.13, p. 224. The squared norm
    is used inside the scalar cutoff, keeping
    the formula smooth at the origin. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormClassHigherUP
  NormHigherDifferentialConstant NormClassHigherArithmetic
  NormClassHigherLocalValues NormClassHigherComposition NormClassHigherRestriction
  NormClassInfinityQuadratic NormClassHigherLocal ScalarCoefficients ScalarUnitCutoffUP ScalarUnitCutoffSealed
  ScalarUnitCutoffSmooth NormUnitBumpUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section BumpWitness.
Variable R : realType.
Variable X : lmodType R.
Variable N : X->R.
Variable B : X->X->R^o.
Hypothesis hN : is_real_norm N.
Hypothesis hB : norm_squared_bilinear_form N B.

(** Source for [norm_unit_bump_witness]:
    a choice of the radial cutoff mu
    of Federer 3.1.13, p. 224.
    The allowed smooth cutoff is chosen as
    g((|x|^2-1)/3), using g from 3.1.11,
    p. 223. This has the same
    unit and double-radius plateau properties. *)
Definition norm_unit_bump_witness (x : X) : R :=
  @ScalarUnitCutoff.value R ((B x x-1)/3).

(** Source for [norm_unit_bump_witness_laws]:
    the range, plateau and radial properties
    of mu in Federer 3.1.13, p. 224,
    proved for the chosen squared-norm witness. *)
Theorem norm_unit_bump_witness_laws :
  is_norm_unit_bump N norm_unit_bump_witness.
Proof.
have hg := @ScalarUnitCutoff.laws R.
have hthree : (0 : R)<3 by lra.
constructor.
- move=> x; exact: (scalar_unit_cutoff_bounds hg _).
- move=> x hx; apply: (scalar_unit_cutoff_lower hg).
  rewrite (hB.2 x) ler_pdivrMr // mul0r.
  have hn := real_seminorm_nonnegative hN.1 x; nra.
- move=> x hx; apply: (scalar_unit_cutoff_upper hg).
  rewrite (hB.2 x) ler_pdivlMr // mul1r; nra.
- move=> x y he; by rewrite /norm_unit_bump_witness !hB.2 he.
Qed.

(** Source for [norm_unit_bump_witness_smooth]:
    mu is of class infinity, Federer
    3.1.13, p. 224. Its argument
    is a continuous quadratic polynomial, and
    composition with the already proved scalar
    cutoff preserves every differentiability class. *)
Theorem norm_unit_bump_witness_smooth
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) R^o)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space N
      (fun t : R^o=>`|t|) (@ez k) (@ZN k)) :
  norm_class_infinity N (fun t : R^o=>`|t|) ez ZN
    (fun _=>True) norm_unit_bump_witness.
Proof.
pose absN := fun t : R^o=>`|t|.
have hAbs := @scalar_absolute_value_norm R.
have hopen x (_ : True) : norm_domain_interior N (fun _=>True) x.
  exists 1; split; first exact: ltr01; by move=>v hv.
have hquad := @norm_class_infinity_quadratic R X R^o N absN hN hAbs
  Z ez ZN hZ (fun _=>True) B hopen hB.1.
have hconst := @norm_class_infinity_constant R X R^o N absN hN hAbs
  Z ez ZN hZ (fun _=>True) hopen (-1).
pose P j := @ContinuousMultilinear.space R j R^o R^o absN absN hAbs hAbs.
pose ep j := @ContinuousMultilinear.evaluation R j R^o R^o absN absN hAbs hAbs.
pose PN j := @ContinuousMultilinear.norm R j R^o R^o absN absN hAbs hAbs.
have hP j : is_continuous_multilinear_space absN absN (ep j) (PN j).
  exact: ContinuousMultilinear.laws.
have hcut := @scalar_unit_cutoff_class_infinity R P ep PN hP.
move=> k.
have hs := norm_class_higher_scale hN hAbs hZ (3 : R)^-1
  (norm_class_higher_add hN hAbs hZ (hquad k) (hconst k)).
have hq : norm_class_higher N absN ez ZN (fun _=>True) (fun x=>(B x x-1)/3) k.
  apply: (@norm_class_higher_domain_agreement R X R^o N absN hN hAbs
    Z ez ZN hZ (fun _=>True) (fun x=>(3 : R)^-1*:(B x x+(-1)))
    (fun x=>(B x x-1)/3) k _ hs).
  move=>x _; change ((3 : R)^-1*(B x x-1)=(B x x-1)/3); ring.
have hc := @norm_class_higher_composition R X N hN k R^o R^o
  absN absN hAbs hAbs Z P Z ez ZN ep PN ez ZN hZ hP hZ
  (fun _=>True) (fun _=>True) (fun x=>(B x x-1)/3)
  (@ScalarUnitCutoff.value R) hq (hcut k).
apply: (@norm_class_higher_open_restriction R X R^o N absN hN hAbs
  Z ez ZN hZ (fun _=>True /\ True) (fun _=>True)
  norm_unit_bump_witness k _ hopen hc).
by move=>x _; split.
Qed.
End BumpWitness.

(** Source for [scalar_squared_norm_bilinear]:
    the scalar squared norm supports a smooth
    scalar radial profile, Federer 3.1.13, p. 224. *)
Lemma scalar_squared_norm_bilinear (R : realType) :
  norm_squared_bilinear_form (fun t : R^o=>`|t|) (fun s t : R^o=>s*t).
Proof.
split.
- split; first exact: scalar_bilinear.
  exists 1; split; first exact: ler01.
  by move=>s t; rewrite normrM mul1r.
- by move=>t; rewrite -normrX (ger0_norm (sqr_ge0 t)) expr2.
Qed.

(** Source for [norm_unit_bump_profile_witness]:
    a smooth choice of gamma in Federer
    3.1.13, p. 224. On
    nonnegative t it has the same squared
    argument as the vector bump; below zero
    it is one, as the printed plateau requires. *)
Definition norm_unit_bump_profile_witness (R : realType) (t : R) :=
  if t<=0 then 1 else @norm_unit_bump_witness R R^o (fun s t=>s*t) t.

(** Source for [norm_unit_bump_profile_witness_laws]:
    the exact scalar range and plateaus for
    gamma, Federer 3.1.13, p. 224. *)
Lemma norm_unit_bump_profile_witness_laws (R : realType) :
  is_scalar_radial_cutoff (@norm_unit_bump_profile_witness R).
Proof.
have hmu := @norm_unit_bump_witness_laws R R^o (fun t : R^o=>`|t|)
  (fun s t=>s*t) (@scalar_absolute_value_norm R) (@scalar_squared_norm_bilinear R).
constructor.
- move=>t; rewrite /norm_unit_bump_profile_witness; case:(t<=0); first by rewrite ler01 lexx.
  exact: (norm_unit_bump_range hmu).
- move=>t ht; rewrite /norm_unit_bump_profile_witness; case ht0:(t<=0)=>//.
  apply: (norm_unit_bump_inner hmu).
  have hp : 0<t by rewrite ltNge ht0.
  by rewrite (ger0_norm (ltW hp)).
- move=>t ht; rewrite /norm_unit_bump_profile_witness.
  have hp : 0<t by lra.
  have hn : ~~(t<=0) by rewrite -ltNge.
  rewrite (negPf hn); apply: (norm_unit_bump_outer hmu).
  by rewrite (ger0_norm (ltW hp)).
Qed.

(** Source for [norm_unit_bump_profile_nonnegative]:
    on nonnegative arguments the smooth profile
    agrees with the squared-norm cutoff used
    to prove existence, Federer 3.1.13, p. 224. *)
Lemma norm_unit_bump_profile_nonnegative (R : realType) (t : R) :
  0<=t -> norm_unit_bump_profile_witness t=
    @ScalarUnitCutoff.value R ((t^+2-1)/3).
Proof.
move=>ht; rewrite /norm_unit_bump_profile_witness; case ht0:(t<=0).
- have -> : t=0 by apply/eqP; rewrite eq_le ht ht0.
  symmetry; apply: (scalar_unit_cutoff_lower (ScalarUnitCutoff.laws R)).
  have h3 : (0:R)<3 by lra.
  rewrite expr0n sub0r ler_pdivrMr // mul0r; lra.
- by rewrite /norm_unit_bump_witness expr2.
Qed.

(** Source for [norm_unit_bump_witness_radial_profile]:
    the exact identity mu(x)=gamma(|x|)
    in Federer 3.1.13, p. 224,
    for the proved smooth scalar profile. *)
Lemma norm_unit_bump_witness_radial_profile (R : realType)
    (X : lmodType R) (N : X->R) (B : X->X->R^o)
    (hN : is_real_norm N) (hB : norm_squared_bilinear_form N B) x :
  @norm_unit_bump_witness R X B x=norm_unit_bump_profile_witness (N x).
Proof.
rewrite (norm_unit_bump_profile_nonnegative (real_seminorm_nonnegative hN.1 x)).
by rewrite /norm_unit_bump_witness hB.2.
Qed.

(** Source for [norm_unit_bump_profile_witness_smooth]:
    gamma is of class infinity on all
    R, including zero, Federer 3.1.13,
    p. 224. Below one it
    is locally constant; above zero it
    is the smooth squared-argument cutoff. *)
Theorem norm_unit_bump_profile_witness_smooth (R : realType)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space (fun t : R^o=>`|t|)
      (fun t : R^o=>`|t|) (@ev i) (@ZN i)) :
  norm_class_infinity (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    ev ZN (fun _=>True) (@norm_unit_bump_profile_witness R).
Proof.
have hAbs := @scalar_absolute_value_norm R.
have hq := @norm_unit_bump_witness_smooth R R^o (fun t : R^o=>`|t|)
  (fun s t=>s*t) hAbs (@scalar_squared_norm_bilinear R) Z ev ZN hZ.
move=>k; apply: (norm_class_higher_local hAbs hAbs hZ)=>a _.
case ha:(a<1).
- pose O (t : R) := t<1.
  have hopen t (ht : O t) : norm_domain_interior (fun x : R^o=>`|x|) O t.
    exists (1-t); split; first by rewrite subr_gt0.
    move=>v hv; have hnorm := ler_norm v; rewrite /O; lra.
  exists O; split; first exact ha; split; first by move=>x hx.
  have hc := @norm_class_infinity_constant R R^o R^o
    (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) hAbs hAbs
    Z ev ZN hZ O hopen 1 k.
  apply: (@norm_class_higher_domain_agreement R R^o R^o
    (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) hAbs hAbs
    Z ev ZN hZ O (fun _=>1) (@norm_unit_bump_profile_witness R) k _ hc).
  move=>t ht; symmetry; exact: (scalar_radial_cutoff_lower
    (@norm_unit_bump_profile_witness_laws R) (ltW ht)).
- pose O (t : R) := 0<t.
  have hap : O a.
    have hge : 1<=a by rewrite leNgt ha.
    exact: (lt_le_trans ltr01 hge).
  have hopen t (ht : O t) : norm_domain_interior (fun x : R^o=>`|x|) O t.
    exists t; split; first exact ht.
    move=>v hv; have hnorm := ler_norm (-v); rewrite normrN in hnorm.
    rewrite /O; lra.
  exists O; split; first exact hap; split; first by move=>x hx.
  have hc := norm_class_higher_open_restriction hAbs hAbs hZ
    (fun x (_ : O x)=>I) hopen (hq k).
  apply: (@norm_class_higher_domain_agreement R R^o R^o
    (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) hAbs hAbs Z ev ZN hZ O
    (@norm_unit_bump_witness R R^o (fun s t=>s*t))
    (@norm_unit_bump_profile_witness R) k _ hc).
  move=>t ht; rewrite /norm_unit_bump_profile_witness.
  have hn : ~~(t<=0) by rewrite -ltNge.
  by rewrite (negPf hn).
Qed.
