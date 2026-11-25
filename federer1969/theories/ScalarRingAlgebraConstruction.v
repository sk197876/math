(** Private hierarchy adapter supporting Federer (1969),
    3.4.8(8), p. 329. Reuse the project's
    ring scalar restriction to regard the original
    scalar ring as an algebra. This allows
    the existing quotient-algebra proof to be reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import TensorUP Bilinear AlgebraUP RingScalarRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Algebra.
Variable K:fieldType.
Variable A:comNzRingType.
Variable scalar:{rmorphism K->A}.
Local Notation V:=([the lmodType K of ring_restricted_space scalar A^o]).

(** Source for [scalar_ring_algebra_bilinear]: multiplication
    is bilinear over the original scalar constants,
    supporting the quotient in 3.4.8(8), p. 329. *)
Lemma scalar_ring_algebra_bilinear:bilinear (fun x y:V=>((x:A)*(y:A):V)).
Proof.
split=>[y c x z|x c y z].
- change ((scalar c*x+z)*y = scalar c*(x*y)+z*y).
  by rewrite mulrDl mulrA.
- change (x*(scalar c*y+z) = scalar c*(x*y)+x*z).
  by rewrite mulrDr mulrA (mulrC x (scalar c)) -mulrA.
Qed.

(** Source for [scalar_ring_algebra]: a private algebra
    witness with the actual original multiplication,
    supporting the reused quotient of 1.3.1, p. 13,
    in 3.4.8(8), p. 329. *)
Definition scalar_ring_algebra:algebra K:=
  @Algebra K V (fun x y:V=>((x:A)*(y:A):V)) (1:A)
    scalar_ring_algebra_bilinear (@mulrA A) (@mul1r A) (@mulr1 A).

(** Source for [scalar_ring_algebra_multiply]: the private
    algebra uses original multiplication, supporting
    3.4.8(8), p. 329. *)
Lemma scalar_ring_algebra_multiply (x y:scalar_ring_algebra):
  alg_mul scalar_ring_algebra x y = (x:A)*(y:A).
Proof. by []. Qed.

(** Source for [scalar_ring_algebra_one]: the private
    algebra uses the original unit, supporting
    3.4.8(8), p. 329. *)
Lemma scalar_ring_algebra_one:alg_one scalar_ring_algebra = (1:A).
Proof. by []. Qed.
End Algebra.
