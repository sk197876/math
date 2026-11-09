(** Federer (1969), 3.3.19, p. 302: elementary
    all-integer small-angle control, derived from the
    Archimedean ordered-real background. Every positive
    scalar cutoff is retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ArchimedeanReciprocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [natural_scaled_reciprocal_tail]: for any
    positive scalar p, the original angles p/n tend
    to zero over all sufficiently large positive integers,
    supporting the cutoff choice in 3.3.19, p. 302. *)
Theorem natural_scaled_reciprocal_tail (R:realType) (p d:R):
  0<p ->0<d ->exists N:nat,forall n,(N<=n)%N ->
    (0<n)%N /\p/n%:R<d.
Proof.
move=>hp hd.
have hpN:p!= 0 by rewrite gt_eqF.
have hRatio:0<d/p by rewrite divr_gt0.
have [J hJ]:=real_reciprocal_below hRatio.
exists J.+1=>n hn.
have hnP:(0<n)%N:=leq_trans (ltn0Sn J) hn.
have hNP:(0<n%:R:>R) by rewrite ltr0n.
have hJP:(0<J.+1%:R:>R) by rewrite ltr0n.
have hCompare:((n%:R:R)^-1<=J.+1%:R^-1) by rewrite lef_pV2 // ler_nat.
have hSmall:=le_lt_trans hCompare hJ.
have hScaled:p/n%:R<p*(d/p) by rewrite ltr_pM2l.
rewrite (mulrC p (d/p)) (divfK hpN) in hScaled.
by split.
Qed.
