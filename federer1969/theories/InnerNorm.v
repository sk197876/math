(** Federer (1969), 1.7.1, p. 28: the norm induced by an inner product. This
    public interface derives its consequences solely from the sealed
    nonnegative-square-root specification. Source context are recorded in
    InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNormUP InnerNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_norm]: Federer 1.7.1, p. 28,
    the associated norm, accessed through its sealed specification. *)
Definition inner_norm (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B) := @InnerNorm.norm R V B hB.

Section Norm.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation N := (inner_norm hB).

(** Source for [inner_norm_laws]: Federer 1.7.1, p. 28,
    the public norm satisfies its nonnegative square-root laws. *)
Lemma inner_norm_laws : is_inner_norm B N.
Proof. exact: InnerNorm.laws. Qed.

(** Source for [inner_norm_nonnegative]: Federer 1.7.1,
    p. 28, the norm is nonnegative. *)
Lemma inner_norm_nonnegative x : 0 <= N x.
Proof. exact: inner_norm_nonnegative_law inner_norm_laws x. Qed.

(** Source for [inner_norm_sqr]: Federer 1.7.1, p. 28,
    the square of the norm equals the diagonal inner product. *)
Lemma inner_norm_sqr x : N x ^+ 2 = B x x.
Proof. exact: inner_norm_square_law inner_norm_laws x. Qed.

(** Source for [inner_norm_value]: Federer 1.7.1, p. 28,
    supporting uniqueness of the prescribed norm at a point. *)
Lemma inner_norm_value x r : 0 <= r -> r ^+ 2 = B x x -> N x = r.
Proof.
move=> hr he; apply/eqP; rewrite eq_le; apply/andP; split.
- by rewrite -(ler_sqr (inner_norm_nonnegative x) hr) inner_norm_sqr he.
- by rewrite -(ler_sqr hr (inner_norm_nonnegative x)) inner_norm_sqr he.
Qed.

(** Source for [inner_norm_eq0]: Federer 1.7.1, p. 28,
    positive definiteness of the norm. *)
Lemma inner_norm_eq0 x : (N x == 0) = (x == 0).
Proof. by rewrite -sqrf_eq0 inner_norm_sqr (inner_self_eq0 hB). Qed.

(** Source for [inner_norm0]: Federer 1.7.1, p. 28,
    the zero vector has norm zero. *)
Lemma inner_norm0 : N 0 = 0.
Proof. by apply/eqP; rewrite inner_norm_eq0. Qed.

(** Source for [inner_norm_gt0]: Federer 1.7.1, p. 28,
    the norm is strictly positive exactly on nonzero vectors. *)
Lemma inner_norm_gt0 x : (0 < N x) = (x != 0).
Proof. by rewrite lt_def inner_norm_nonnegative andbT inner_norm_eq0. Qed.

(** Source for [inner_normZ]: Federer 1.7.1, p. 28,
    absolute homogeneity of the norm defined by the inner product.
    This follows directly by squaring and nonnegativity. *)
Lemma inner_normZ a x : N (a *: x) = `|a| * N x.
Proof.
apply: inner_norm_value; first exact: mulr_ge0 (normr_ge0 a) (inner_norm_nonnegative x).
by rewrite exprMn -normrX ger0_norm ?sqr_ge0 // inner_norm_sqr (inner_scale_square hB).
Qed.

(** Source for [inner_normN]: Federer 1.7.1, p. 28,
    symmetry of the norm, needed for the induced metric. *)
Lemma inner_normN x : N (-x) = N x.
Proof. by rewrite -scaleN1r inner_normZ normrN normr1 mul1r. Qed.
End Norm.
