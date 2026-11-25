(** Federer (1969), 3.4.5, p. 320: existence
    and uniqueness of the original one-equation variety germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LocalGermUP LocalGermSealed
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRingLaws SetGermUP SetGermExistence AnalyticZeroGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_zero_germ_exists]: local equality
    of analytic functions gives local equality of their
    zero sets, 3.4.5, pp. 319–320. *)
Theorem analytic_zero_germ_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (alpha:analytic_germ_space hNX a):
  exists sigma,@is_analytic_zero_germ R X NX hNX a alpha sigma.
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose P:=@analytic_representative_type R X NX hNX a.
pose value:=@analytic_representative_value R X NX hNX a.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
exists (@set_germ T a [set x|value f x=0])=>g hg.
have hEqual:analytic_germ g=analytic_germ f by rewrite hf hg.
have [U [hU [ha hValues]]]:=(local_germ_equality (@LocalGerms.laws T R P value a) g f).1 hEqual.
apply/set_germ_equality_original;exists U;split;first exact:hU.
split;first exact:ha.
apply/seteqP;split.
- move=>x [hx hu];split;last exact:hu.
  change (value f x=0);by rewrite -(hValues x hu).
- move=>x [hx hu];split;last exact:hu.
  change (value g x=0);by rewrite (hValues x hu).
Qed.

(** Source for [analytic_zero_germ_unique]: the original
    all-representative equation specifies exactly one germ,
    3.4.5, p. 320. *)
Lemma analytic_zero_germ_unique (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (alpha:analytic_germ_space hNX a) sigma tau:
  @is_analytic_zero_germ R X NX hNX a alpha sigma ->
  @is_analytic_zero_germ R X NX hNX a alpha tau ->sigma=tau.
Proof.
move=>hSigma hTau;have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
by rewrite -(hSigma f hf) -(hTau f hf).
Qed.
