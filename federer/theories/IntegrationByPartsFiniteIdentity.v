(** Federer (1969), 2.9.24, p. 169: right-endpoint values of f and
    left-endpoint values of g give the finite telescoping identity before
    bounded convergence. This is the same identity as 2.5.18(1), p. 112. The
    factor in the second summand is g(t_j). *)
From mathcomp Require Import all_boot all_order all_algebra reals topology ring lra.
From Federer Require Import StieltjesSums StieltjesIntegral StieltjesIntegrationByParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [integration_by_parts_cell_identity]: direct one-cell
    telescoping identity in Federer 2.9.24, p. 169, using the right f value
    and the left g value. *)
Lemma integration_by_parts_cell_identity (R : realType) (fa fb ga gb : R) :
  fb*(gb-ga)+ga*(fb-fa)=fb*gb-fa*ga.
Proof. ring. Qed.

(** Source for [integration_by_parts_uniform_identity]: direct finite
    identity in Federer 2.9.24, p. 169, with n+1 uniform
    cells and right-endpoint f values. The existing tagged-list
    identity from 2.5.18(1), p. 112, supplies telescoping;
    no continuity or bounded variation is used in this algebraic step. *)
Lemma integration_by_parts_uniform_identity (R : realType) (f g : R -> R)
    (a b : R) (n : nat) :
  stieltjes_sum f g (uniform_right_tagged a ((b-a)/n.+1%:R) n.+1)+
    stieltjes_sum g f (uniform_partition a b n)=f b*g b-f a*g a.
Proof.
have hi := @uniform_parts_identity R f g a ((b-a)/n.+1%:R) n.+1.
have he : a+n.+1%:R*((b-a)/n.+1%:R)=b.
  by rewrite mulrC mulfVK ?pnatr_eq0 // addrC subrK.
by rewrite he in hi.
Qed.

(** Source for [right_tagged_cell_excess]: Supporting check for Federer
    2.9.24, p. 169: using right endpoints for both factors adds exactly
    Delta f times Delta g to the one-cell boundary expression. *)
Lemma right_tagged_cell_excess (R : realType) (fa fb ga gb : R) :
  fb*(gb-ga)+gb*(fb-fa)-(fb*gb-fa*ga)=(fb-fa)*(gb-ga).
Proof. ring. Qed.

(** Source for [right_tagged_cell_counterexample]: Supporting check for
    Federer 2.9.24, p. 169: for f=g=identity on [0,1], using right endpoints
    for both factors gives two instead of the boundary value one. *)
Lemma right_tagged_cell_counterexample (R : realType) :
  (1*(1-0)+1*(1-0) : R) != 1*1-0*0.
Proof. apply/eqP=> he; lra. Qed.
