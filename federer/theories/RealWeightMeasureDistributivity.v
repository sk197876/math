(** Federer (1969), 2.4.1, p. 81: combine r*f(r,s) and s*f(r,s) into
    (r+s)*f(r,s). Infinite measures are retained; 0 times infinity is zero.
    Source context: MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_weight_measure_distributivity]: supporting
    partial-arithmetic identity in Federer 2.4.1, p. 81 *)
Lemma real_weight_measure_distributivity (R : realType) (r s : R) (t : \bar R) :
  0 <= t -> adde_def (r%:E*t) (s%:E*t) -> (r+s)%:E*t = r%:E*t+s%:E*t.
Proof.
case: t=> [t| |] ht hd; last by [].
- by rewrite -!EFinM -EFinD mulrDl.
case: (eqVneq r 0%R)=> [->|hr0]; first by rewrite add0r mul0e add0e.
case: (eqVneq s 0%R)=> [->|hs0]; first by rewrite addr0 mul0e adde0.
have [hr|hr] := ltP 0%R r; have [hs|hs] := ltP 0%R s.
- rewrite EFinD; apply: ge0_muleDl; rewrite lee_fin; exact: ltW.
- have hs' : (s < 0)%R by rewrite lt_neqAle hs0 hs.
  by move: hd; rewrite (mulry r) (mulry s) (gtr0_sg hr) (ltr0_sg hs') mul1e mulN1e.
- have hr' : (r < 0)%R by rewrite lt_neqAle hr0 hr.
  by move: hd; rewrite (mulry r) (mulry s) (ltr0_sg hr') (gtr0_sg hs) mulN1e mul1e.
- rewrite EFinD; apply: le0_muleDl; by rewrite lee_fin.
Qed.
