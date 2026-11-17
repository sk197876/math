(** Federer (1969), corrected 3.4.8(11), pp. 327, 333:
    the finite irreducible reduction uses each component
    with every original analytic starting set. Keep the
    given actual representative as an existence invariant;
    all resulting strata must lie inside it. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness SetGermUP FiniteAnalyticVarietyUP AnalyticFiniteStratificationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section GermStatement.
Variable R:realType.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).

(** Source for [analytic_stratification_for_germ]:
    the uniform component existence statement in the
    ordered reduction of 3.4.8(11), p. 333.
    These independent requirements assume no component
    decomposition or finite-component conclusion. *)
Definition analytic_stratification_for_germ (alpha:@set_germ_space T 0):Prop:=
  forall U H U0 S0:set X,U 0 ->@is_finite_analytic_variety R X NX hNX U H ->
    @set_germ T 0 H=alpha ->U0 0 ->@is_finite_analytic_variety R X NX hNX U0 S0 ->
    exists mu,exists V S G:'I_mu->set X,
      @is_analytic_finite_stratification R n alpha (@set_germ T 0 S0) m U0 S0 mu V S G /\
      forall i,S i `<=` H.
End GermStatement.
