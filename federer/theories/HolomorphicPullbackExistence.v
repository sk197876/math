(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: the original
    representative equation induces one and only one map on germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives RealNormUP NormMetric HolomorphicAtUP LocalGermUP LocalGermSealed
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws
  HolomorphicPullbackRepresentative HolomorphicPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Existence.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable NY:Y->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Hypothesis hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY.
Variable A:set X.
Variable u:X->Y.
Variable a:X.
Hypothesis hu:@is_holomorphic_at R X Y NX NY hNX hNY A u a.

(** Source for [holomorphic_germ_pullback_exists]: existence
    of the induced germ map of 3.4.5, p. 319.
    Selected representatives remain local to this proof. *)
Theorem holomorphic_germ_pullback_exists:
  exists P:holomorphic_germ_space hNY (u a)->holomorphic_germ_space hNX a,
    is_holomorphic_germ_pullback hu P.
Proof.
pose repr alpha:=projT1 (cid (@holomorphic_germ_has_representative R Y NY hNY (u a) alpha)).
have hRepr alpha:holomorphic_germ (repr alpha)=alpha:=
  projT2 (cid (@holomorphic_germ_has_representative R Y NY hNY (u a) alpha)).
exists (fun alpha=>holomorphic_germ (@holomorphic_pullback_representative R X Y NX NY hNX hNY A u a hu (repr alpha)))=>f.
apply/(local_germ_equality (@LocalGerms.laws (Topological.clone (real_norm_metric_space hNX) _)
  (ComplexScalars.C R) _ (@holomorphic_representative_value R X NX hNX a) a)).
apply:holomorphic_pullback_preserves_local_equality.
apply/(local_germ_equality (@LocalGerms.laws (Topological.clone (real_norm_metric_space hNY) _)
  (ComplexScalars.C R) _ (@holomorphic_representative_value R Y NY hNY (u a)) (u a))).
exact:hRepr.
Qed.

(** Source for [holomorphic_germ_pullback_unique]: uniqueness
    from every original representative equation, 3.4.5, p. 319. *)
Theorem holomorphic_germ_pullback_unique
    (P Q:holomorphic_germ_space hNY (u a)->holomorphic_germ_space hNX a):
  is_holomorphic_germ_pullback hu P ->is_holomorphic_germ_pullback hu Q ->P=Q.
Proof.
move=>hP hQ;apply:funext=>alpha.
have [f <-]:=@holomorphic_germ_has_representative R Y NY hNY (u a) alpha.
by rewrite (hP f) (hQ f).
Qed.
End Existence.
