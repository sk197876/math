(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 321: the
    ideal of an original finite union is the intersection
    of the corresponding original vanishing ideals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws
  SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder SetGermFiniteUnion
  HolomorphicGermVanishingUP HolomorphicGermVanishingSealed HolomorphicGermVanishingRepresentative HolomorphicGermVanishingMonotonicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Ideals.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=(@set_germ_space T a).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX a).

(** Source for [holomorphic_empty_set_ideal_whole]: every
    analytic germ vanishes on the empty set germ,
    including the empty component-family case in 3.4.5, p. 321. *)
Lemma holomorphic_empty_set_ideal_whole (alpha:holomorphic_germ_space hNX a):
  ideal (@set_germ T a set0) alpha.
Proof.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
rewrite -hf;apply/(holomorphic_set_ideal_representative_equation f set0).
exists setT;split;first exact:openT.
split;first exact:Logic.I.
by move=>x hx;case:hx.
Qed.

(** Source for [holomorphic_set_ideal_union]: the ideal of
    two original germs' union is their ideal intersection,
    supporting 3.4.5, p. 321. *)
Lemma holomorphic_set_ideal_union (sigma tau:G):
  ideal (@SetGerms.join T a sigma tau)=ideal sigma `&` ideal tau.
Proof.
apply/seteqP;split.
- move=>alpha hAlpha;split.
  + exact:((@holomorphic_set_ideal_antitone R X NX hNX a sigma _ (set_germ_subset_join_left sigma tau)) _ hAlpha).
  + exact:((@holomorphic_set_ideal_antitone R X NX hNX a tau _ (set_germ_subset_join_right sigma tau)) _ hAlpha).
- move=>alpha [hSigma hTau].
  have [S hS]:=@set_germ_has_representative T a sigma.
  have [V hV]:=@set_germ_has_representative T a tau.
  have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
  rewrite -hS -hV -hf in hSigma hTau *.
  rewrite (@set_germ_union_equation T a _ _ _ (@SetGerms.laws T a)).
  apply/(holomorphic_set_ideal_representative_equation f (S `|` V)).
  have [U [hU [ha hF]]]:=(holomorphic_set_ideal_representative_equation f S).1 hSigma.
  have [W [hW [hb hG]]]:=(holomorphic_set_ideal_representative_equation f V).1 hTau.
  exists (U `&` W);split;first exact:openI hU hW.
  split;first by split.
  by move=>x [hx|hx] [hu hw];[exact:hF x hx hu|exact:hG x hx hw].
Qed.

(** Source for [holomorphic_set_ideal_finite_union]: a germ
    vanishes on the finite original union exactly when it
    vanishes on every original member, 3.4.5, p. 321. *)
Lemma holomorphic_set_ideal_finite_union (F:seq G) (alpha:holomorphic_germ_space hNX a):
  ideal (@set_germ_finite_union T a F) alpha <->forall beta,beta \in F ->ideal beta alpha.
Proof.
elim:F=>[|sigma F ih].
- split;first by move=>_ beta;rewrite in_nil.
  move=>_;exact:holomorphic_empty_set_ideal_whole.
- change (ideal (@SetGerms.join T a sigma (@set_germ_finite_union T a F)) alpha <->forall beta,beta \in sigma::F ->ideal beta alpha).
  rewrite holomorphic_set_ideal_union;split.
  + move=>[hSigma /ih hF] beta;rewrite in_cons;move/orP=>[/eqP ->|hBeta];first exact:hSigma.
    exact:hF beta hBeta.
  + move=>hAll;split.
    * exact:hAll sigma (mem_head sigma F).
    * apply/ih=>beta hBeta;apply:hAll;by rewrite in_cons hBeta orbT.
Qed.
End Ideals.
