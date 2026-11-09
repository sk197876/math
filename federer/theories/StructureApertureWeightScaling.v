(** Federer (1969), 3.3.4, p. 289: exact finite aperture-weight
    scaling before the zero and infinite limit comparisons. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_aperture_weight_scaling]: supporting the
    bounded u(s)/s argument of Federer 3.3.4, p. 289. Dilating the
    aperture by a positive finite c changes its degree-m weight by
    exactly c^m, even for an infinite original numerator. *)
Lemma structure_aperture_weight_scaling (R:realType) m (b: \bar R) (r s c:R):
  0<c ->
  (b*((r^-1)^+m)%:E*((s^-1)^+m)%:E=
    (c^+m)%:E*(b*((r^-1)^+m)%:E*(((c*s)^-1)^+m)%:E))%E.
Proof.
move=>hc.
have hScale:(s^-1)^+m=c^+m*((c*s)^-1)^+m.
  by symmetry; rewrite invfM exprMn mulrA -exprMn mulfV ?gt_eqF // expr1n mul1r.
have hE:((c^+m)%:E*(((c*s)^-1)^+m)%:E=((s^-1)^+m)%:E)%E.
  by rewrite -EFinM -hScale.
rewrite -hE; exact:muleCA.
Qed.
