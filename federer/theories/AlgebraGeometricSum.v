(** Federer (1969), 3.1.11, p. 220:
    finite geometric sums in an associative algebra.
    The two telescoping identities do not assume commutativity
    of the ambient algebra. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP AlgebraPowers Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [algebra_geometric_sum]: finite partial
    sums of the inverse series in Federer 3.1.11,
    p. 220, before taking its norm limit. *)
Definition algebra_geometric_sum (K : fieldType) (A : algebra K) (x : A) n :=
  \sum_(i<n) @AlgebraPowers.algebra_power K A x i.

(** Source for [algebra_geometric_sum_zero]: the empty
    partial sum is zero, supporting the series convention
    of Federer 3.1.11, p. 220. *)
Lemma algebra_geometric_sum_zero (K : fieldType) (A : algebra K) (x : A) :
  algebra_geometric_sum x 0= 0.
Proof. by rewrite /algebra_geometric_sum big_ord0. Qed.

(** Source for [algebra_geometric_sum_successor]:
    consecutive partial sums differ by the next power,
    supporting Federer 3.1.11, p. 220. *)
Lemma algebra_geometric_sum_successor (K : fieldType) (A : algebra K) (x : A) n :
  algebra_geometric_sum x n.+1=
    algebra_geometric_sum x n+@AlgebraPowers.algebra_power K A x n.
Proof. by rewrite /algebra_geometric_sum big_ord_recr. Qed.

(** Source for [algebra_power_multiply_right]:
    an element commutes with its own powers, supporting
    the right inverse identity in Federer 3.1.11,
    p. 220. No general commutativity is assumed. *)
Lemma algebra_power_multiply_right (K : fieldType) (A : algebra K) (x : A) n :
  alg_mul A (@AlgebraPowers.algebra_power K A x n) x=
    @AlgebraPowers.algebra_power K A x n.+1.
Proof.
by rewrite -{2}(AlgebraPowers.algebra_power1 x) -AlgebraPowers.algebra_power_add addn1.
Qed.

(** Source for [algebra_geometric_sum_left]:
    the left telescoping identity for finite inverse
    sums, supporting Federer 3.1.11, p. 220. *)
Lemma algebra_geometric_sum_left (K : fieldType) (A : algebra K) (x : A) n :
  alg_mul A (alg_one A-x) (algebra_geometric_sum x n)=
    alg_one A-@AlgebraPowers.algebra_power K A x n.
Proof.
elim: n=> [|n ih].
- by rewrite algebra_geometric_sum_zero (bil0r (alg_bilinear A))
    AlgebraPowers.algebra_power0 subrr.
- rewrite algebra_geometric_sum_successor (bilDr (alg_bilinear A)) ih
    (bilBl (alg_bilinear A)) alg_unitl.
  change ((alg_one A-@AlgebraPowers.algebra_power K A x n)+
    (@AlgebraPowers.algebra_power K A x n-@AlgebraPowers.algebra_power K A x n.+1)=
      alg_one A-@AlgebraPowers.algebra_power K A x n.+1).
  by rewrite addrA subrK.
Qed.

(** Source for [algebra_geometric_sum_right]:
    the right telescoping identity for finite inverse
    sums, supporting Federer 3.1.11, p. 220. *)
Lemma algebra_geometric_sum_right (K : fieldType) (A : algebra K) (x : A) n :
  alg_mul A (algebra_geometric_sum x n) (alg_one A-x)=
    alg_one A-@AlgebraPowers.algebra_power K A x n.
Proof.
elim: n=> [|n ih].
- by rewrite algebra_geometric_sum_zero (bil0l (alg_bilinear A))
    AlgebraPowers.algebra_power0 subrr.
- rewrite algebra_geometric_sum_successor (bilDl (alg_bilinear A)) ih
    (bilBr (alg_bilinear A)) alg_unitr algebra_power_multiply_right.
  by rewrite addrA subrK.
Qed.
