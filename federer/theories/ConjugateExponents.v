(** Federer (1969), 2.4.14, p. 88, and the choice q=p/(p-1) in the proof of
    2.4.15, p. 89. These are elementary scalar supporting facts, not
    additional numbered assertions. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_conjugate_exponents_strict]: reconciliation of the
    finite-exponent hypotheses in Federer 2.4.14, p. 88. For finite real
    p,q, the printed weak lower bounds and reciprocal identity force both
    exponents strictly above one. *)
Lemma finite_conjugate_exponents_strict (R : realType) (p q : R) :
  1 <= p -> 1 <= q -> p^-1+q^-1 = 1 -> 1 < p /\ 1 < q.
Proof.
move=> hp hq hpq.
have hp0 := lt_le_trans (ltr01) hp.
have hq0 := lt_le_trans (ltr01) hq.
have hpne : p != 1.
  apply/negP=> /eqP he.
  have hlt : 1 < p^-1+q^-1 by rewrite he invr1 ltrDl invr_gt0.
  by move: hlt; rewrite hpq ltxx.
have hqne : q != 1.
  apply/negP=> /eqP he.
  have hlt : 1 < p^-1+q^-1 by rewrite he invr1 ltrDr invr_gt0.
  by move: hlt; rewrite hpq ltxx.
by split; rewrite lt_neqAle eq_sym ?hpne ?hqne ?hp ?hq.
Qed.

(** Source for [finite_conjugate_exponent]: the exponent chosen
    in Federer 2.4.15, proof p. 89, to apply
    Holder's inequality 2.4.14. Only p>1 is specified. *)
Definition finite_conjugate_exponent (R : realType) (p : R) := p/(p-1).

(** Source for [finite_conjugate_exponent_strict]: admissibility of the
    chosen exponent in Federer 2.4.15, p. 89 *)
Lemma finite_conjugate_exponent_strict (R : realType) (p : R) :
  1 < p -> 1 < finite_conjugate_exponent p.
Proof.
move=> hp; have hd : 0 < p-1 by rewrite subr_gt0.
by rewrite /finite_conjugate_exponent ltr_pdivlMr // mul1r ltrBlDl ltrDr ltr01.
Qed.

(** Source for [finite_conjugate_exponent_reciprocals]: reciprocal
    identity required by Federer 2.4.14, p. 88,
    for the explicit exponent in 2.4.15, p. 89. *)
Lemma finite_conjugate_exponent_reciprocals (R : realType) (p : R) :
  1 < p -> p^-1+(finite_conjugate_exponent p)^-1 = 1.
Proof.
move=> hp; have hp0 := lt_trans (ltr01) hp.
have he : 1+(p-1)=p by rewrite addrC subrK.
by rewrite /finite_conjugate_exponent invf_div -{1}[p^-1]mul1r -mulrDl he mulfV ?gt_eqF.
Qed.

(** Source for [finite_conjugate_exponent_product]: the scalar identity
    (p-1)q=p used in the norm computation in Federer 2.4.15, p. 89 *)
Lemma finite_conjugate_exponent_product (R : realType) (p : R) :
  1 < p -> (p-1)*finite_conjugate_exponent p = p.
Proof.
move=> hp; have hd : p-1 != 0 by rewrite subr_eq0 gt_eqF.
by rewrite /finite_conjugate_exponent mulrCA mulfV // mulr1.
Qed.
