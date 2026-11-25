(** Federer (1969), 3.4.8(1),(2), p. 326:
    pointed coordinate pullbacks preserve the actual ring
    operations. The independent representative laws prove
    these identities before a hierarchy adapter is constructed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermSealed AnalyticGermRingLaws AnalyticGermRing PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section RingLaws.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Variables (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variables (a:X) (b:Y) (u:X->Y).
Variable P:analytic_germ_space hNY b->analytic_germ_space hNX a.
Hypothesis hP:is_pointed_analytic_germ_pullback u P.
Local Notation GY:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY b)].
Local Notation GX:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].

(** Source for [pointed_analytic_pullback_add]: the original
    coordinate pullback preserves addition, supporting
    3.4.8(1),(2), p. 326. *)
Lemma pointed_analytic_pullback_add (alpha beta:GY):
  P (alpha+beta)=(P alpha:GX)+(P beta:GX).
Proof.
have [f <-]:=@analytic_germ_has_representative R Y NY hNY b alpha.
have [g <-]:=@analytic_germ_has_representative R Y NY hNY b beta.
have [pf [hPF hVF]]:=hP f;have [pg [hPG hVG]]:=hP g.
have [ps [hPS hVS]]:=hP (@analytic_add_representatives R Y NY hNY b f g).
change (P (@AnalyticGerms.add R Y NY hNY b (analytic_germ f) (analytic_germ g))=
  @AnalyticGerms.add R X NX hNX a (P (analytic_germ f)) (P (analytic_germ g))).
rewrite (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R Y NY hNY b))
  hPS hPF hPG (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x.
change (analytic_representative_value ps x=analytic_representative_value pf x+analytic_representative_value pg x).
by rewrite hVS hVF hVG.
Qed.

(** Source for [pointed_analytic_pullback_multiply]: the original
    coordinate pullback preserves multiplication, supporting
    3.4.8(1),(2), p. 326. *)
Lemma pointed_analytic_pullback_multiply (alpha beta:GY):
  P (alpha*beta)=(P alpha:GX)*(P beta:GX).
Proof.
have [f <-]:=@analytic_germ_has_representative R Y NY hNY b alpha.
have [g <-]:=@analytic_germ_has_representative R Y NY hNY b beta.
have [pf [hPF hVF]]:=hP f;have [pg [hPG hVG]]:=hP g.
have [ps [hPS hVS]]:=hP (@analytic_multiply_representatives R Y NY hNY b f g).
change (P (@AnalyticGerms.mul R Y NY hNY b (analytic_germ f) (analytic_germ g))=
  @AnalyticGerms.mul R X NX hNX a (P (analytic_germ f)) (P (analytic_germ g))).
rewrite (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R Y NY hNY b))
  hPS hPF hPG (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
apply:analytic_germ_pointwise_equality=>x.
change (analytic_representative_value ps x=analytic_representative_value pf x*analytic_representative_value pg x).
by rewrite hVS hVF hVG.
Qed.

(** Source for [pointed_analytic_pullback_constant]: the original
    coordinate pullback preserves scalar constants, including
    zero and one, supporting 3.4.8(1),(2), p. 326. *)
Lemma pointed_analytic_pullback_constant (c:R):
  P (analytic_germ (@analytic_constant_representative R Y NY hNY b c))=
    analytic_germ (@analytic_constant_representative R X NX hNX a c).
Proof.
have [g [hG hValues]]:=hP (@analytic_constant_representative R Y NY hNY b c).
rewrite hG;apply:analytic_germ_pointwise_equality=>x.
exact:hValues x.
Qed.
End RingLaws.
