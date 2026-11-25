(** Federer (1969), 3.2.36, p. 272:
    a finite nonnegative radius polynomial has
    uniformly small positive-degree terms. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unit_interval_positive_power_le]:
    elementary support for the Steiner radius
    estimate in Federer 3.2.36, p. 272.
    Every positive natural power of a radius
    in [0,1] is bounded by that radius.
    This is infrastructure, not an additional
    theorem attributed to the book. *)
Lemma unit_interval_positive_power_le (R:realType) (r:R):
  0<=r ->r<=1 ->forall j:nat,(0<j)%N ->r^+j<=r.
Proof.
move=>hr hr1.
have hPowNonnegative j:0<=r^+j by apply:exprn_ge0; exact:hr.
have hPower:forall j:nat,r^+j<=1.
  elim=>[|j hj]; first by rewrite expr0.
  rewrite exprS; apply:le_trans (ler_pM hr (hPowNonnegative j) hr1 hj) _.
  by rewrite mul1r.
case=>[|j] // _; rewrite exprS.
apply:le_trans (ler_pM hr (hPowNonnegative j) (lexx r) (hPower j)) _.
by rewrite mulr1.
Qed.

(** Source for [nonnegative_reverse_polynomial_small_radius_bound]:
    supporting compact-convex volume continuity
    in Federer 3.2.36, p. 272.
    The Steiner polynomial minus its constant
    term is bounded by r times the
    sum of its coefficients for 0<=r<=1.
    All finite degrees, including ambient zero,
    are included. No uniform geometric bound
    is assumed in this elementary scalar lemma. *)
Lemma nonnegative_reverse_polynomial_small_radius_bound (R:realType) n
    (a:'I_n.+1->R) (r:R):
  (forall i,0<=a i) ->0<=r ->r<=1 ->
  \sum_(i:'I_n.+1) a i*r^+(n-i) <=a ord_max+r* \sum_i a i.
Proof.
move=>ha hr hr1.
have hPartial:(\sum_(i:'I_n) a (widen_ord (leqnSn n) i))<=\sum_i a i.
  rewrite [X in _<=X]big_ord_recr lerDl; exact:ha.
have hPowNonnegative j:0<=r^+j by apply:exprn_ge0; exact:hr.
have hTerms:(\sum_(i:'I_n) a (widen_ord (leqnSn n) i)*r^+(n-i))<=
    r* \sum_(i:'I_n) a (widen_ord (leqnSn n) i).
  rewrite mulr_sumr; apply:ler_sum=>i _.
  have hExponent:(0<n-i)%N by rewrite subn_gt0; exact:ltn_ord.
  apply:le_trans (ler_pM (ha _) (hPowNonnegative _) (lexx _)
    (unit_interval_positive_power_le hr hr1 hExponent)) _.
  by rewrite mulrC.
rewrite [X in X<=_]big_ord_recr subnn expr0 mulr1.
apply:le_trans (lerD hTerms (lexx _)) _; rewrite addrC.
apply:lerD; first exact:lexx.
apply:ler_pM; [exact:hr|apply:sumr_ge0=>i _; exact:ha|exact:lexx|exact:hPartial].
Qed.
