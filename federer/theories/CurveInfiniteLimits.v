(** Federer (1969), 2.5.16, p. 110: either sup im s = oo or g(oo) = lim g(x)
    as x tends to oo exists in Y, and either inf im s = -oo or g(-oo) = lim
    g(x) as x tends to -oo exists in Y. The limits are taken along the
    neighbourhood filters of oo and -oo of the analysis library;
    completeness is the Cauchy filter formulation of CompleteMetricUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import CompleteMetricUP CurveVariationUP CurveArcLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InfiniteLimits.
Variable R : realType.
Variable Y : metricType R.
Variable g : R -> Y.
Hypothesis hfin : curve_locally_finite_variation g.
Hypothesis hY : is_complete_metric_space Y.
Local Notation s := (arc_length g).

(** Source for [curve_pinfty_cauchy]: when im s is bounded above, the
    image filter of g at oo is Cauchy, Federer 2.5.16, p. 110, by
    p[g(t), g(u)] <= s(u) - s(t) <= sup im s - s(t). *)
Lemma curve_pinfty_cauchy : has_ubound (range s) -> cauchy (g @ +oo).
Proof.
move=> hub; apply/cauchyP=> e he.
have hsup : has_sup (range s) by split=> //; exists (s 0), 0.
have [_ [t0 _ <-] ht0] := sup_adherent he hsup.
exists (g t0).
suff : \forall t \near +oo, ball (g t0) e (g t) by [].
near=> t; rewrite ballEmdist.
have ht0t : t0 <= t by near: t; exact: nbhs_pinfty_ge (num_real t0).
apply: le_lt_trans (arc_length_distance hfin ht0t) _.
rewrite ltrBlDr; apply: le_lt_trans (sup_upper_bound hsup _) _; first by exists t.
by rewrite addrC -ltrBlDr.
Unshelve. all: end_near.
Qed.

(** Source for [curve_limit_at_pinfty]: existence of
    g(oo) = lim g(x) as x tends to oo when sup im s < oo, Federer
    2.5.16, p. 110, by completeness. *)
Theorem curve_limit_at_pinfty : has_ubound (range s) -> exists y : Y, g @ +oo --> y.
Proof.
move=> hub.
exact: hY _ (fmap_proper_filter g proper_pinfty_nbhs) (curve_pinfty_cauchy hub).
Qed.

(** Source for [curve_pinfty_dichotomy]: either sup im s = oo or g(oo)
    exists, Federer 2.5.16, p. 110. *)
Theorem curve_pinfty_dichotomy : ~ has_ubound (range s) \/ exists y : Y, g @ +oo --> y.
Proof.
case: (pselect (has_ubound (range s)))=> h; last by left.
by right; exact: curve_limit_at_pinfty.
Qed.

(** Source for [curve_ninfty_cauchy]: when im s is bounded below, the
    image filter of g at -oo is Cauchy, Federer 2.5.16, p. 110. *)
Lemma curve_ninfty_cauchy : has_lbound (range s) -> cauchy (g @ -oo).
Proof.
move=> [M hM]; apply/cauchyP=> e he.
have hsup : has_sup [set - s t | t in [set: R]].
  split; first by exists (- s 0), 0.
  by exists (- M)=> _ [t _ <-]; rewrite lerN2; apply: hM; exists t.
have [_ [t0 _ <-] ht0] := sup_adherent he hsup.
exists (g t0).
suff : \forall t \near -oo, ball (g t0) e (g t) by [].
near=> t; rewrite ballEmdist /= metric_sym.
have htt0 : t <= t0 by near: t; exact: nbhs_ninfty_le (num_real t0).
apply: le_lt_trans (arc_length_distance hfin htt0) _.
have hst : - sup [set - s t | t in [set: R]] <= s t.
  by rewrite lerNl; apply: (sup_upper_bound hsup); exists t.
apply: le_lt_trans (lerB (lexx (s t0)) hst) _.
rewrite opprK addrC -ltrBrDr; move: ht0.
by rewrite ltrBlDr [- s t0 + e]addrC.
Unshelve. all: end_near.
Qed.

(** Source for [curve_limit_at_ninfty]: existence of
    g(-oo) = lim g(x) as x tends to -oo when inf im s > -oo, Federer
    2.5.16, p. 110, by completeness. *)
Theorem curve_limit_at_ninfty : has_lbound (range s) -> exists y : Y, g @ -oo --> y.
Proof.
move=> hlb.
exact: hY _ (fmap_proper_filter g proper_ninfty_nbhs) (curve_ninfty_cauchy hlb).
Qed.

(** Source for [curve_ninfty_dichotomy]: either inf im s = -oo or
    g(-oo) exists, Federer 2.5.16, p. 110. *)
Theorem curve_ninfty_dichotomy : ~ has_lbound (range s) \/ exists y : Y, g @ -oo --> y.
Proof.
case: (pselect (has_lbound (range s)))=> h; last by left.
by right; exact: curve_limit_at_ninfty.
Qed.

End InfiniteLimits.
