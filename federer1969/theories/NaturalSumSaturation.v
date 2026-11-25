(** Federer (1969), 3.4.7, p. 325: equality of
    the degree and order sums forces equality for
    each factor. This elementary natural-number argument supports
    the comparison with the original power t^k. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [natural_equal_sum_bounds_saturated]: two
    upper bounds whose sums agree must both be
    attained, supporting the polynomial order argument
    in 3.4.7, p. 325. *)
Lemma natural_equal_sum_bounds_saturated r s m n:
  r<=m ->s<=n ->r+s = m+n ->r = m /\s = n.
Proof.
move=>hRM hSN hSum.
have hR:r = m.
  case:(eqVneq r m)=>[h|hDifferent];first exact:h.
  have hStrict:r<m by rewrite ltn_neqAle hDifferent hRM.
  have hStep:r+n<m+n by rewrite ltn_add2r.
  have hTotal:=leq_ltn_trans (leq_add (leqnn r) hSN) hStep.
  by rewrite hSum ltnn in hTotal.
split;first exact:hR.
have hEqual:m+s = m+n by rewrite -{1}hR.
have h:=congr1 (fun k:nat=>(k-m)%N) hEqual.
by rewrite !addKn in h.
Qed.
