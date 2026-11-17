(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: existence
    and uniqueness of the original one-equation variety germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric LocalGermUP LocalGermSealed
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws SetGermUP SetGermExistence HolomorphicZeroGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_zero_germ_exists]: local equality
    of analytic functions gives local equality of their
    zero sets, 3.4.5, pp. 319–320. *)
Theorem holomorphic_zero_germ_exists (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) (alpha:holomorphic_germ_space hNX a):
  exists sigma,@is_holomorphic_zero_germ R X NX hNX a alpha sigma.
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
pose P:=@holomorphic_representative_type R X NX hNX a.
pose value:=@holomorphic_representative_value R X NX hNX a.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
exists (@set_germ T a [set x|value f x=0])=>g hg.
have hEqual:holomorphic_germ g=holomorphic_germ f by rewrite hf hg.
have [U [hU [ha hValues]]]:=(local_germ_equality (@LocalGerms.laws T (ComplexScalars.C R) P value a) g f).1 hEqual.
apply/set_germ_equality_original;exists U;split;first exact:hU.
split;first exact:ha.
apply/seteqP;split.
- move=>x [hx hu];split;last exact:hu.
  change (value f x=0);by rewrite -(hValues x hu).
- move=>x [hx hu];split;last exact:hu.
  change (value g x=0);by rewrite (hValues x hu).
Qed.

(** Source for [holomorphic_zero_germ_unique]: the original
    all-representative equation specifies exactly one germ,
    3.4.5, p. 320. *)
Lemma holomorphic_zero_germ_unique (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) (alpha:holomorphic_germ_space hNX a) sigma tau:
  @is_holomorphic_zero_germ R X NX hNX a alpha sigma ->
  @is_holomorphic_zero_germ R X NX hNX a alpha tau ->sigma=tau.
Proof.
move=>hSigma hTau;have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
by rewrite -(hSigma f hf) -(hTau f hf).
Qed.
