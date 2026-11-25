(** Federer (1969), 3.1.24, p. 239: the
    rational composition identity computing the coefficient sum. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import ScalarAnalyticFraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_analytic_fraction_composition_domain]: supporting
    the scalar special case in Federer 3.1.24, p. 239.
    Where both factors of the composition are defined, the
    denominator 1-c(gamma+1)x of its simplified expression is
    nonzero. The actual composition domain is retained. *)
Lemma scalar_analytic_fraction_composition_domain (R:realType) (c g x:R) :
  scalar_analytic_fraction_domain c x ->
  scalar_analytic_fraction_domain g (scalar_analytic_fraction c x) ->
  scalar_analytic_fraction_domain (c*(g+1)) x.
Proof.
rewrite /scalar_analytic_fraction_domain=>hF hG.
have he:(-g*scalar_analytic_fraction c x+1)*(-c*x+1)= -(c*(g+1))*x+1.
  rewrite /scalar_analytic_fraction; field; exact hF.
have hh:=mulf_neq0 hG hF.
by rewrite he in hh.
Qed.

(** Source for [scalar_analytic_fraction_composition_value]: the
    identity (g composed with f)(x)=c gamma x/[1-c(gamma+1)x]
    in Federer 3.1.24, p. 239. Express it as
    gamma/(gamma+1) times the same rational function with
    parameter c(gamma+1), so its actual derivatives are
    supplied by the already proved scalar fraction fields. *)
Lemma scalar_analytic_fraction_composition_value (R:realType) (c g x:R) :
  g+1!=0 -> scalar_analytic_fraction_domain c x ->
  scalar_analytic_fraction_domain g (scalar_analytic_fraction c x) ->
  scalar_analytic_fraction g (scalar_analytic_fraction c x)=
    (g/(g+1))*scalar_analytic_fraction (c*(g+1)) x.
Proof.
move=>hg hF hG.
have hH:=scalar_analytic_fraction_composition_domain hF hG.
move:hF hG hH; rewrite /scalar_analytic_fraction_domain /scalar_analytic_fraction=>hF hG hH.
field; by rewrite hH hg hF.
Qed.
