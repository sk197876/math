(** Federer (1969), 3.4.5, p. 321: actual
    analytic Taylor coefficient fields remain analytic along
    the axis in the cited example. This finite scalar
    estimate iterates the derivative bound from 3.1.24,
    pp. 237–239; it is an internal supporting lemma. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import AnalyticSuccessorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_shifted_factorial_bound_exists]:
    a fixed finite derivative shift preserves factorial
    analytic growth with a proved finite constant, supporting
    actual coefficient analyticity in the example cited at
    3.4.5, p. 321. No infinite series majorant
    or derivative-bound hypothesis is added. *)
Theorem analytic_shifted_factorial_bound_exists (R:realType) (c:R) k:
  0<=c ->exists C:R,0<=C /\forall q,(1<=q)%N ->
    c^+(k+q)*(k+q)`!%:R<=C^+q*(q`!)%:R.
Proof.
move=>hc;elim:k=>[|k [C [hC hBound]]].
- exists c;split;first exact:hc. by move=>q hq;rewrite add0n.
- exists ((C+1)*(2 * C));split.
  + apply:mulr_ge0;[exact:addr_ge0 hC ler01|exact:mulr_ge0 (ler0n R 2) hC].
  + move=>q hq.
    have hEstimate:=hBound q.+1 (leq0n q).
    have hShift:(k+q.+1=k.+1+q)%N by rewrite addnS addSn.
    rewrite hShift in hEstimate.
    apply:le_trans hEstimate _.
    exact:(@analytic_successor_factorial_bound R C q hC hq).
Qed.
