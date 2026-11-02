(** Federer (1969), 1.7.1, p. 28: the usual dot product on R^n, sum_i x_i
    y_i. The proof includes n=0 and specifies the inner-product laws before
    verifying this coordinate witness. Source context are recorded in
    InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Euclidean.
Variable R : realFieldType.
Variable n : nat.
Local Notation E := (R_n R n).

(** Source for [euclidean_inner_product]: Federer 1.7.1,
    p. 28, the displayed coordinate formula for the dot product. *)
Definition euclidean_inner_product (x y : E) : R := \sum_i x i * y i.

(** Source for [euclidean_inner_bilinear]: Federer 1.7.1,
    p. 28, supporting verification of bilinearity of the coordinate example. *)
Lemma euclidean_inner_bilinear : @TensorUP.bilinear R E E R^o euclidean_inner_product.
Proof.
split.
- move=> y a x z; rewrite /euclidean_inner_product.
  under eq_bigr do rewrite !ffunE.
  change ((\sum_i (a * x i + z i) * y i) = a * (\sum_i x i * y i) + \sum_i z i * y i).
  under eq_bigr do rewrite mulrDl -mulrA.
  by rewrite big_split mulr_sumr.
- move=> x a y z; rewrite /euclidean_inner_product.
  under eq_bigr do rewrite !ffunE.
  change ((\sum_i x i * (a * y i + z i)) = a * (\sum_i x i * y i) + \sum_i x i * z i).
  under eq_bigr do rewrite mulrDr [x _ * (a * _)]mulrCA.
  by rewrite big_split mulr_sumr.
Qed.

(** Source for [euclidean_inner_symmetric]: Federer 1.7.1,
    p. 28, supporting symmetry of the coordinate dot product. *)
Lemma euclidean_inner_symmetric x y : euclidean_inner_product x y = euclidean_inner_product y x.
Proof. apply: eq_bigr => i _; exact: mulrC. Qed.

(** Source for [euclidean_inner_nonnegative]: Federer
    1.7.1, p. 28, the coordinate diagonal is a sum of squares. *)
Lemma euclidean_inner_nonnegative x : 0 <= euclidean_inner_product x x.
Proof. apply: sumr_ge0 => i _; by rewrite -expr2 sqr_ge0. Qed.

(** Source for [euclidean_inner_eq0]: Federer 1.7.1,
    p. 28, the sum of the coordinate squares vanishes exactly
    when every coordinate vanishes. *)
Lemma euclidean_inner_eq0 x : (euclidean_inner_product x x == 0) = (x == 0).
Proof.
apply/idP/idP.
- move/eqP=> h; apply/eqP/ffunP=> i; rewrite ffunE.
  have hs : \sum_j (x j)^+2 = 0.
    by under eq_bigr do rewrite expr2.
  have hi := psumr_eq0P (fun j _ => sqr_ge0 (x j)) hs (i:=i) isT.
  by apply/eqP; rewrite -sqrf_eq0 hi eqxx.
- move/eqP=> ->; apply/eqP; apply: big1 => i _; by rewrite ffunE mul0r.
Qed.

(** Source for [euclidean_inner_productP]: Federer 1.7.1,
    p. 28, the displayed coordinate function is an inner product.
    The zero-dimensional space satisfies the same laws. *)
Theorem euclidean_inner_productP : is_inner_product euclidean_inner_product.
Proof.
constructor; [exact: euclidean_inner_bilinear | exact: euclidean_inner_symmetric |].
by move=> x; rewrite lt_def euclidean_inner_nonnegative andbT euclidean_inner_eq0.
Qed.
End Euclidean.
