(** Federer (1969), 3.4.5, pp. 320–321:
    analytic variety germs contain the whole and empty germs
    and are closed under the induced union and intersection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermUP AnalyticGermSealed SetGermUP SetGermSealed
  AnalyticVarietyGermUP AnalyticZeroGermSealed AnalyticZeroGermLaws AnalyticZeroGermSquares AnalyticZeroGermVarieties.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Closure.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation V sigma:=(@is_analytic_variety_germ R X NX hNX a sigma).

(** Source for [analytic_variety_germ_empty]: the empty
    germ is defined by the unit equation, 3.4.5, p. 320. *)
Lemma analytic_variety_germ_empty:V (@set_germ T a set0).
Proof. rewrite -(@analytic_zero_germ_one R X NX hNX a);exact:analytic_zero_germ_is_variety. Qed.

(** Source for [analytic_variety_germ_whole]: the whole
    germ is defined by the zero equation, 3.4.5, p. 320. *)
Lemma analytic_variety_germ_whole:V (@set_germ T a setT).
Proof. rewrite -(@analytic_zero_germ_zero R X NX hNX a);exact:analytic_zero_germ_is_variety. Qed.

(** Source for [analytic_variety_germ_union]: the original
    union of two variety germs is a variety germ,
    3.4.5, p. 320. *)
Lemma analytic_variety_germ_union (alpha beta:@set_germ_space T a):
  V alpha ->V beta ->V (@SetGerms.join T a alpha beta).
Proof.
move=>hAlpha hBeta.
have [f <-]:=@analytic_variety_germ_single_equation R X NX hNX a alpha hAlpha.
have [g <-]:=@analytic_variety_germ_single_equation R X NX hNX a beta hBeta.
rewrite -analytic_zero_germ_product;exact:analytic_zero_germ_is_variety.
Qed.

(** Source for [analytic_variety_germ_intersection]: the
    original intersection of two variety germs is a variety
    germ, 3.4.5, p. 320. *)
Lemma analytic_variety_germ_intersection (alpha beta:@set_germ_space T a):
  V alpha ->V beta ->V (@SetGerms.meet T a alpha beta).
Proof.
move=>hAlpha hBeta.
have [f <-]:=@analytic_variety_germ_single_equation R X NX hNX a alpha hAlpha.
have [g <-]:=@analytic_variety_germ_single_equation R X NX hNX a beta hBeta.
rewrite -analytic_zero_germ_square_sum;exact:analytic_zero_germ_is_variety.
Qed.
End Closure.
