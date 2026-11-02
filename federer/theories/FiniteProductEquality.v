(** Federer (1969), 1.7.5, p. 32: supporting equality criterion for products
    of nonnegative bounds. This scalar infrastructure isolates the
    zero-factor exception in the corrected statement. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nonnegative_product_equality]: Federer
    1.7.5, p. 32, supporting scalar criterion: equality between
    products of bounded nonnegative factors holds exactly when the
    upper product vanishes or every individual bound is an equality. *)
Lemma nonnegative_product_equality (R : realFieldType) (I : finType)
    (a b : I -> R) (hab : forall i, 0 <= a i <= b i) :
  ((\prod_i a i) == (\prod_i b i)) =
    ((\prod_i b i) == 0) || [forall i, a i == b i].
Proof.
have hh := @leif_pprod R I predT (fun i => a i == b i) a b
  (fun i _ => (andP (hab i)).1) (fun i _ => leif_eq (andP (hab i)).2).
exact hh.2.
Qed.
