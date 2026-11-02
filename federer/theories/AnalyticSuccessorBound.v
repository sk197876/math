(** Federer (1969), 3.2.33, p. 270: analytic
    differentials and hence analytic rank tests. Supporting
    factorial-bound absorption from 3.1.24, p. 237. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import AnalyticArithmeticBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [natural_successor_power_two_bound]: supporting
    closure of analytic functions under differentiation in the
    analytic discussion of Federer 3.2.33, p. 270.
    Absorb the factor q+1 into a geometric bound. *)
Lemma natural_successor_power_two_bound q:(q.+1<=2^q)%N.
Proof.
elim:q=>[|q ih]; first by [].
rewrite expnS mul2n -addnn.
apply:leq_trans (_:q.+2<=q.+1+q.+1)%N (leq_add ih ih).
by rewrite addnS leq_addr.
Qed.

(** Source for [analytic_successor_factorial_bound]: the actual
    qth derivative of Df has the norm of D^(q+1)f,
    supporting the analytic h_i in Federer 3.2.33,
    p. 270, by the defining factorial bound of 3.1.24,
    p. 237. A single finite constant works for every
    positive order; c=0 is retained without division. *)
Lemma analytic_successor_factorial_bound (R:realType) (c:R) q:
  0<=c ->(1<=q)%N ->
  c^+q.+1*(q.+1`!)%:R<=((c+1)*(2*c))^+q*(q`!)%:R.
Proof.
move=>hc hq.
have hNat:(q.+1%:R:R)<=(2:R)^+q.
  rewrite -natrX ler_nat; exact:natural_successor_power_two_bound.
have hNonnegative:0<=c*c^+q*(q`!)%:R.
  exact:(mulr_ge0 (mulr_ge0 hc (exprn_ge0 q hc)) (ler0n R (q`!))).
have hFirst:=ler_wpM2l hNonnegative hNat.
have hIdentity:c^+q.+1*(q.+1`!)%:R=(c*c^+q*(q`!)%:R)*q.+1%:R.
  rewrite exprS factS natrM; ring.
rewrite hIdentity.
apply:le_trans hFirst _.
have hEq:(c*c^+q*(q`!)%:R)*(2:R)^+q=c*(2*c)^+q*(q`!)%:R.
  rewrite exprMn; ring.
rewrite hEq.
apply:ler_wpM2r; first exact:ler0n.
have hTwo:0<=(2:R) by rewrite ler0n.
exact:(analytic_scalar_factor_bound hc (mulr_ge0 hTwo hc) hq).
Qed.
