(** Federer (1969), 3.3.4, p. 291:
    clear the positive aperture square in
    the projective-ball inequality. The exact
    single-coordinate cone coefficient is retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_projective_angle_equation]:
    the final scalar equivalence in the
    displayed inverse-image computation of Federer
    3.3.4, p. 291. The actual strict
    projective ball inequality is exactly the
    coordinate-cone inequality after clearing t^2>0. *)
Lemma structure_projective_angle_equation (R:realType) (a b t:R):
  0<t ->(a<t^+2*(a+b) <->((t^-1)^+2-1)*a<b).
Proof.
move=>ht.
have ht2:0<t^+2 by rewrite exprn_gt0.
have hCleared:((t^-1)^+2*a<a+b)=(a<t^+2*(a+b)).
  by rewrite exprVn mulrC (ltr_pdivrMr _ _ ht2) mulrC.
rewrite -hCleared; split=>h; nra.
Qed.
