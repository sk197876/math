(** Federer (1969), 1.7.11, p. 36: the scalar factors
    2^(-1/2) in the source basis and 2^(1/2) in its image.
    Supporting square-root identities include the coefficient that
    multiplies the active exterior product. Source context:
    ProductInnerUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inverse_sqrt_two_square]: Federer 1.7.11,
    p. 36, supporting normalisation: twice the square of 1/sqrt(2)
    is one, so diagonal and antidiagonal vectors have unit length. *)
Lemma inverse_sqrt_two_square (R : rcfType) :
  ((Num.sqrt (2 : R))^-1)^+2 * (2 : R) = 1.
Proof.
rewrite exprVn sqr_sqrtr ?ler0n // mulVf //.
by rewrite pnatr_eq0.
Qed.

(** Source for [twice_inverse_sqrt_two]: Federer 1.7.11,
    p. 36, the image of the normalised antidiagonal vector
    is sqrt(2) times its common ambient vector. *)
Lemma twice_inverse_sqrt_two (R : rcfType) :
  (2 : R) * (Num.sqrt (2 : R))^-1 = Num.sqrt (2 : R).
Proof.
have hp : 0 < Num.sqrt (2 : R) by rewrite sqrtr_gt0 ltr0n.
have hn : Num.sqrt (2 : R) != 0 := lt0r_neq0 hp.
have h2n : 0 <= (2 : R) by rewrite ler0n.
by rewrite -{1}(sqr_sqrtr h2n) expr2 -mulrA mulfV // mulr1.
Qed.
