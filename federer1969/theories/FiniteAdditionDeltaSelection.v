(** Federer (1969), 3.4.5, p. 321: exact
    finite additive-index selection supporting the original
    quadratic remainder coefficient identities. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import FiniteRectangularDeltaSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [finite_addition_delta_selection]: the
    original nonnegative index solving i+B=N is retained
    precisely when B<=N, supporting 3.4.5, p. 321.
    The finite cutoff N+1 always includes that solution. *)
Theorem finite_addition_delta_selection (V:zmodType) (N B:nat) (F:nat->V):
  (\sum_(i<N.+1 | (i+B==N)%N) F i)=
    if (B<=N)%N then F (N-B)%N else 0.
Proof.
case hB:(B<=N)%N.
- have hSplit:(N-B+B=N)%N:=subnK hB.
  have hTest (i:nat):(i+B==N)%N=(i==N-B)%N.
    by rewrite -{1}hSplit eqn_add2r.
  have hSum:(\sum_(i<N.+1 | (i+B==N)%N) F i)=
      \sum_(i<N.+1) if ((i:nat)==N-B)%N then F i else 0.
    rewrite [LHS]big_mkcond;by apply:eq_bigr=>i _;rewrite hTest.
  have hBound:(N-B<N.+1)%N by rewrite ltnS;exact:leq_subr.
  by rewrite hSum finite_ordinal_delta_sum hBound.
- apply:big1=>i /eqP hEqual.
  have hLe:(B<=i+B)%N:=leq_addl i B.
  by rewrite hEqual hB in hLe.
Qed.
