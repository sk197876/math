(** Federer (1969), 3.2.36, p. 273:
    the exact second-factor tube radius
    in a first-distance fibre is sqrt(r^2-s^2). *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [pythagorean_radius_cutoff]:
    supporting the exact tube-fibre identity
    in the second displayed equality of
    Federer 3.2.36, p. 273.
    Nonnegative actual distances with a^2=s^2+b^2
    satisfy a<r exactly when b<sqrt(r^2-s^2),
    for 0<=s<r. Positivity and the
    actual nonnegative square-root law justify
    squaring both comparisons; no default
    root or extra radius assumption is used. *)
Lemma pythagorean_radius_cutoff (R:realType) (a b s r:R):
  0<=a ->0<=b ->0<=s ->s<r ->a^+2=s^+2+b^+2 ->
  (a<r)=(b<Num.sqrt (r^+2-s^+2)).
Proof.
move=>ha hb hs hsr hSquare.
have hr:0<r:=le_lt_trans hs hsr.
have hDifference:0<r^+2-s^+2.
  by rewrite subr_gt0 (ltr_sqr hs (ltW hr)).
rewrite -(ltr_sqr ha (ltW hr)) -(ltr_sqr hb (sqrtr_ge0 _))
  (sqr_sqrtr (ltW hDifference)) hSquare.
by rewrite ltrBrDl addrC.
Qed.
