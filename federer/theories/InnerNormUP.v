(** Federer (1969), 1.7.1, p. 28: |x| is the nonnegative square root of x.x.
    We specify this value by its two determining laws, before choosing a
    square-root construction. Source context are recorded in
    InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_inner_norm]: Federer 1.7.1, p. 28,
    definition of |x|. The two square-root laws characterise the
    norm associated with a given inner product. *)
Record is_inner_norm (R : realFieldType) (V : lmodType R)
  (B : V -> V -> R) (N : V -> R) : Prop := {
  inner_norm_nonnegative_law : forall x, 0 <= N x;
  inner_norm_square_law : forall x, N x ^+ 2 = B x x
}.

(** Source for [inner_norm_unique]: Federer 1.7.1, p. 28,
    uniqueness implicit in the nonnegative square-root definition.
    This proof uses only the determining laws. *)
Theorem inner_norm_unique (R : realFieldType) (V : lmodType R)
  (B : V -> V -> R) (N M : V -> R) :
  is_inner_norm B N -> is_inner_norm B M -> N =1 M.
Proof.
move=> hN hM x; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -(ler_sqr (inner_norm_nonnegative_law hN x) (inner_norm_nonnegative_law hM x)).
  by rewrite (inner_norm_square_law hN) (inner_norm_square_law hM).
- rewrite -(ler_sqr (inner_norm_nonnegative_law hM x) (inner_norm_nonnegative_law hN x)).
  by rewrite (inner_norm_square_law hN) (inner_norm_square_law hM).
Qed.
