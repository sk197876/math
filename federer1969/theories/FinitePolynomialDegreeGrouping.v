(** Federer (1969), 3.2.36, p. 273: regroup a finite
    polynomial by its natural radius degree before coefficient comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_polynomial_degree_grouping]: the regrouping
    by xi+eta in the third display of Federer 3.2.36, p. 273.
    Finite partition and distributivity collect all terms of a given
    radius degree. There is no positivity requirement on coefficients
    and no external polynomial library. *)
Lemma finite_polynomial_degree_grouping (R:realType) (I:finType) N
    (degree:I->'I_N.+1) (c:I->R) (r:R):
  \sum_i c i*r^+(degree i)=
    \sum_(d:'I_N.+1) (\sum_(i|degree i==d) c i)*r^+d.
Proof.
rewrite (partition_big degree predT) //=.
apply:eq_bigr=>d _; rewrite mulr_suml.
apply:eq_bigr=>i /eqP he; by rewrite he.
Qed.

(** Source for [finite_complement_degree_grouping]: the same finite
    regrouping for products in Federer 3.2.36, p. 273. The
    degree is (m-i)+(n-j); the conditional coefficient sum retains
    every pair of endpoint indices, including zero-dimensional blocks. *)
Lemma finite_complement_degree_grouping (R:realType) m n
    (c:'I_m.+1->'I_n.+1->R) (r:R):
  \sum_(i:'I_m.+1) \sum_(j:'I_n.+1) c i j*r^+((m-i)+(n-j))=
    \sum_(d:'I_(m+n).+1)
      (\sum_(i:'I_m.+1) \sum_(j:'I_n.+1|
        ((m-i)+(n-j)==d)%N) c i j)*r^+d.
Proof.
pose I:=[the finType of ('I_m.+1*'I_n.+1)%type].
have hBound (p:I):((m-p.1)+(n-p.2)<(m+n).+1)%N.
  by rewrite ltnS; apply:leq_add; exact:leq_subr.
pose degree (p:I):'I_(m+n).+1:=Ordinal (hBound p).
have h:=@finite_polynomial_degree_grouping R I (m+n) degree (fun p=>c p.1 p.2) r.
rewrite pair_bigA.
rewrite h; apply:eq_bigr=>d _; congr (_*r^+d).
rewrite pair_big_dep.
apply:eq_bigl=>p.
by rewrite andTb -val_eqE /degree.
Qed.
