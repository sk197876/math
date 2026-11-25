(** Federer (1969), 3.2.31, p. 269: supporting the
    two scales of a symmetric approximation. A projection has
    only eigenvalues zero and one, by idempotence. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [idempotent_eigenvalue_zero_or_one]: supporting
    the approximation by symmetric automorphisms in Federer
    3.2.31, p. 269. On a nonzero eigenvector of an
    idempotent linear map, the eigenvalue satisfies c*c=c,
    hence is zero or one. This algebraic support holds over
    every field, without finite dimension or positivity. *)
Lemma idempotent_eigenvalue_zero_or_one (K:fieldType) (V:lmodType K)
    (P:Hom V V) (x:V) (c:K):
  (forall y,P (P y)= P y) ->x!=0 ->P x=c*:x ->c=0 \/c= 1.
Proof.
move=>hIdem hx hEigen.
have hEq:=hIdem x.
rewrite hEigen linearZ in hEq.
change (c*:P x=c*:x) in hEq.
rewrite hEigen scalerA in hEq.
have hZero:(c*c-c)*:x=0 by rewrite scalerBl hEq subrr.
have hScalar:c*c-c=0.
  apply/eqP; move/eqP:hZero.
  by rewrite scaler_eq0 (negbTE hx) orbF.
have hFactor:c*(c-1)=0 by rewrite mulrBr mulr1; exact hScalar.
move/eqP:hFactor; rewrite mulf_eq0 subr_eq0=>/orP [/eqP h0|/eqP h1].
- by left.
- by right.
Qed.
