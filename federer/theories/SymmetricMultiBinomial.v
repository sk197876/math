(** Federer (1969), 1.9.4, p. 43: the coefficient product of
    binomial(alpha_i,beta_i) in the ordinary monomial diagonal. The
    factorial identity is integral; its inverse form uses characteristic
    zero, sufficient for the book's real scalars. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SymmetricMultiIndices SymmetricExponentBox SymmetricDividedMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_multi_binomial]: Federer 1.9.4,
    p. 43, the product over coordinates of the binomial coefficients. *)
Definition symmetric_multi_binomial n (a b : symmetric_multi_index n) :=
  (\prod_(i < n) 'C(a i,b i))%N.

(** Source for [symmetric_multi_binomial_factorial]: Federer
    1.9.4, p. 43, supporting factorial cancellation identity:
    the binomial product times beta! times (alpha-beta)! equals alpha!. *)
Lemma symmetric_multi_binomial_factorial n (a b : symmetric_multi_index n) :
  (forall i, b i <= a i)%N ->
  (symmetric_multi_binomial a b * (symmetric_multi_factorial b *
    symmetric_multi_factorial (symmetric_multi_difference a b)))%N = symmetric_multi_factorial a.
Proof.
move=> hb; rewrite /symmetric_multi_binomial /symmetric_multi_factorial -!big_split.
apply: eq_bigr=> i _; rewrite /symmetric_multi_difference ffunE.
exact: bin_fact (hb i).
Qed.

(** Source for [symmetric_multi_binomial_cancel]: Federer
    1.9.4, p. 43, the scalar cancellation converting the
    divided monomial formula to the ordinary binomial-coefficient formula. *)
Lemma symmetric_multi_binomial_cancel (K : fieldType) (h0 : [pchar K] =i pred0)
    n (a b : symmetric_multi_index n) (hb : forall i, (b i <= a i)%N) :
  ((symmetric_multi_factorial a)%:R : K) * ((symmetric_multi_factorial b)%:R : K)^-1 *
    ((symmetric_multi_factorial (symmetric_multi_difference a b))%:R : K)^-1 =
      (symmetric_multi_binomial a b)%:R.
Proof.
have hf : ((symmetric_multi_factorial a)%:R : K) =
    (symmetric_multi_binomial a b)%:R *
      ((symmetric_multi_factorial b)%:R * (symmetric_multi_factorial (symmetric_multi_difference a b))%:R).
  by rewrite -!natrM (symmetric_multi_binomial_factorial hb).
rewrite -mulrA -invfM hf mulfK //.
apply: mulf_neq0; exact: (@symmetric_multi_factorial_nonzero K h0).
Qed.
