(** Supporting endpoint bookkeeping for Federer (1969), 2.9.21, p. 166,
    after condition (4) of 2.9.20, pp. 165–166. Zero induced endpoint masses
    permit replacing the open restriction by the closed restriction for a
    globally continuous representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostBasic MeasureRestriction MeasureAbsoluteContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_closed_interval_absolute_continuity]: supporting
    endpoint replacement for Federer 2.9.21, p. 166 If both endpoints have
    zero numerator mass, absolute continuity of its restriction to (a,b)
    implies absolute continuity on [a,b]. No endpoint continuity is assumed
    here; the required zero masses are explicit hypotheses. *)
Lemma open_closed_interval_absolute_continuity (R : realType)
    (phi psi : set R -> \bar R) (a b : R) : is_measure psi ->
  psi [set a]=0 -> psi [set b]=0 ->
  is_absolutely_continuous_measure (measure_restrict psi `]a,b[) phi ->
  is_absolutely_continuous_measure (measure_restrict psi `[a,b]) phi.
Proof.
move=> hm ha hb hAC N hN.
have hOpen := hAC N hN.
have hEnd := @measure_null_union R R psi hm [set a] [set b] ha hb.
have hAll := @measure_null_union R R psi hm (`]a,b[ `&` N)
  ([set a] `|` [set b]) hOpen hEnd.
apply: (@measure_null_subset R R psi hm (`[a,b] `&` N) _) hAll.
move=> x [hx hxN]; move: hx; rewrite /= in_itv /= => /andP[hax hxb].
case: (eqVneq x a)=> [->|hxa]; first by right; left.
case: (eqVneq x b)=> [->|hxb']; first by right; right.
left; split=> //; rewrite /= in_itv /= !lt_neqAle.
by rewrite eq_sym hxa hxb' hax hxb.
Qed.
