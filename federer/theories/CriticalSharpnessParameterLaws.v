(** Federer (1969), 3.4.4, pp. 317–318: the
    original parameter inequalities give the strict Whitney exponent. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_sharpness_holder_exponent]: beta<alpha/k
    implies k<alpha/beta in 3.4.4, p. 318.
    Both denominators are proved strictly positive. *)
Lemma critical_sharpness_holder_exponent (R:realType) k (alpha beta:R):
  (1<=k)%N ->0<beta ->beta<alpha/k%:R ->k%:R<alpha/beta.
Proof.
move=>hK hBeta hBound.
have hk:0<(k%:R:R) by rewrite ltr0n.
have hProduct:beta*k%:R<alpha by move:hBound;rewrite ltr_pdivlMr.
rewrite ltr_pdivlMr //;by rewrite mulrC.
Qed.
