(** Federer (1969), 2.9.24, p. 169: pointwise convergence of f_n passes to
    f_n g' at points where g' is finite. This supporting real sequence law
    permits either sign and zero for that fixed factor. The local Federer
    erratum has no entry for this supporting law. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal lra.
From Federer Require Import ExtendedRealOrderLimit RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_finite_sequence_limit_right_scale]: supporting
    finite multiplication limit in Federer 2.9.24, p. 169.
    The cutoff epsilon/(|c|+1) includes c=0 and both signs. *)
Lemma real_finite_sequence_limit_right_scale (R : realType) (u : nat -> R) (a c : R) :
  extended_order_limit (fun n => (u n)%:E) a%:E ->
  extended_order_limit (fun n => (u n*c)%:E) (a*c)%:E.
Proof.
move=> hu; apply: real_error_extended_order_limit=> e he.
have hc0 := normr_ge0 c.
have hcp : 0<`|c|+1 by lra.
have hep : 0<e/(`|c|+1) by rewrite divr_gt0.
have [N hN] := @extended_finite_order_limit_error R u a _ hu hep.
exists N=> n hn.
have hsmall := hN n hn.
have hprod : (`|c|+1)*`|u n-a|<e.
  by move: hsmall; rewrite ltr_pdivlMr // mulrC.
rewrite -mulrBl normrM.
have hn0 := normr_ge0 (u n-a).
have hcmp : `|u n-a|*`|c|<=(`|c|+1)*`|u n-a| by nra.
exact: le_lt_trans hcmp hprod.
Qed.
