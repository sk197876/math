(** Federer (1969), 3.1.1, p. 211: the coordinate-by-coordinate
    path in the proof that continuous partial derivatives imply
    differentiability. These are auxiliary finite-coordinate formulas. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm EuclideanCoordinateMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinatewise_norm_bound]: supporting
    containment of the coordinate path in the ball of Federer 3.1.1,
    p. 211. Decreasing the absolute value of each coordinate cannot
    increase the Euclidean norm, by its defining sum of squares. *)
Lemma euclidean_coordinatewise_norm_bound (R : realType) n
    (x y : R_n R n) :
  (forall i, `|x i| <= `|y i|) ->
  inner_norm (@euclidean_inner_productP R n) x <=
  inner_norm (@euclidean_inner_productP R n) y.
Proof.
move=> hxy.
rewrite -(ler_sqr (inner_norm_nonnegative _ x) (inner_norm_nonnegative _ y))
  !inner_norm_sqr /euclidean_inner_product.
apply: ler_sum=> i _; rewrite -!expr2.
have hs : `|x i|^+2 <= `|y i|^+2.
  by rewrite (ler_sqr (normr_ge0 _) (normr_ge0 _)); exact: hxy.
by rewrite !real_normK ?num_real in hs.
Qed.

(** Source for [coordinate_prefix]: the increment with its first
    k coordinates retained and the rest zero, supporting the telescoping
    path displayed in Federer 3.1.1, p. 211. *)
Definition coordinate_prefix (R : realType) n (h : R_n R n) (k : nat) : R_n R n :=
  [ffun i : 'I_n => if (i<k)%N then h i else 0].

(** Source for [coordinate_prefix_zero]: the coordinate path of
    Federer 3.1.1, p. 211, starts at the base point. *)
Lemma coordinate_prefix_zero (R : realType) n (h : R_n R n) :
  coordinate_prefix h 0 = 0.
Proof. by apply/ffunP=> i; rewrite /coordinate_prefix !ffunE ltn0. Qed.

(** Source for [coordinate_prefix_full]: the coordinate path of
    Federer 3.1.1, p. 211, ends at the full increment. *)
Lemma coordinate_prefix_full (R : realType) n (h : R_n R n) :
  coordinate_prefix h n = h.
Proof. by apply/ffunP=> i; rewrite /coordinate_prefix ffunE ltn_ord. Qed.

(** Source for [coordinate_prefix_step]: consecutive points in
    the telescoping sum of Federer 3.1.1, p. 211, differ only in the
    next coordinate. *)
Lemma coordinate_prefix_step (R : realType) n (h : R_n R n) (i : 'I_n) :
  coordinate_prefix h i.+1 = coordinate_prefix h i+h i *: (@coordinate_basis R n i).
Proof.
apply/ffunP=> j; rewrite /coordinate_prefix /coordinate_basis !ffunE.
change ((if (j<i.+1)%N then h j else 0) =
  (if (j<i)%N then h j else 0)+h i*(if j==i then 1 else 0)).
case: (eqVneq j i)=> [->|hji].
- by rewrite ltnSn ltnn mulr1 add0r.
- rewrite ltnS leq_eqVlt val_eqE (negPf hji) /= mulr0 addr0.
  by [].
Qed.

(** Source for [coordinate_stair_segment_bound]: every intermediate
    segment in Federer 3.1.1, p. 211, stays in the Euclidean ball
    centred at the base point and passing through the endpoint. *)
Lemma coordinate_stair_segment_bound (R : realType) n (h : R_n R n)
    (i : 'I_n) (t : R) : 0 <= t -> t <= 1 ->
  inner_norm (@euclidean_inner_productP R n)
    (coordinate_prefix h i+(t*h i) *: (@coordinate_basis R n i)) <=
  inner_norm (@euclidean_inner_productP R n) h.
Proof.
move=> ht ht1; apply: euclidean_coordinatewise_norm_bound=> j.
rewrite /coordinate_prefix /coordinate_basis !ffunE.
change (`|(if (j<i)%N then h j else 0)+(t*h i)*(if j==i then 1 else 0)| <= `|h j|).
case: (eqVneq j i)=> [->|hji].
- rewrite ltnn mulr1 add0r normrM (ger0_norm ht).
  by rewrite -{2}(mul1r `|h i|); apply: ler_wpM2r; [exact: normr_ge0|exact ht1].
- rewrite mulr0 addr0.
  case: ifP=> _; first exact: lexx.
  by rewrite normr0 normr_ge0.
Qed.

(** Source for [coordinate_staircase_telescope]: the finite
    telescoping sum in Federer 3.1.1, p. 211, before applying the
    triangle inequality. Dimension zero is included. *)
Lemma coordinate_staircase_telescope (R : realType) n (Y : zmodType)
    (f : R_n R n -> Y) (a h : R_n R n) :
  f (a+h)-f a = \sum_(i<n)
    (f (a+coordinate_prefix h i.+1)-f (a+coordinate_prefix h i)).
Proof.
have ht := @telescope_sumr Y 0 n (fun k => f (a+coordinate_prefix h k)) (leq0n n).
rewrite big_mkord coordinate_prefix_full coordinate_prefix_zero addr0 in ht.
exact: esym ht.
Qed.
