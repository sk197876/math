(** Federer 2.8.9, p. 146, strict-convexity parenthesis. Strict convexity
    is specified by strict midpoint containment on each norm sphere.
    The laws are independent of the radial-projection theorem. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import RealNormUP InnerProductUP InnerNormUP InnerNorm
  InnerNormInequalities InnerTriangleEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_midpoint]: Federer 2.8.9, p. 146;
    supporting ordinary affine midpoint in the original vector space. *)
Definition norm_midpoint (R : realFieldType) (V : lmodType R) (x y : V) : V :=
  (2 : R)^-1 *: (x+y).

(** Source for [is_strictly_convex_norm]: Federer 2.8.9, p. 146;
    abstract strict convexity of norm spheres: the midpoint of distinct
    equal-norm vectors lies strictly inside that sphere. No radial law or
    construction is part of this independent geometric specification. *)
Definition is_strictly_convex_norm (R : realFieldType) (V : lmodType R)
    (N : V -> R) : Prop :=
  forall x y, N x = N y -> x <> y -> N (norm_midpoint x y) < N x.

(** Source for [positive_norm_half]: Federer 2.8.9, p. 146;
    supporting positivity of the midpoint coefficient. *)
Lemma positive_norm_half (R : realFieldType) : 0 < (2 : R)^-1.
Proof. by rewrite invr_gt0 ltr0n. Qed.

(** Source for [norm_half_sum_one]: Federer 2.8.9, p. 146;
    the two midpoint coefficients have sum one. Supporting scalar law. *)
Lemma norm_half_sum_one (R : realFieldType) : (2:R)^-1 + (2:R)^-1 = 1.
Proof.
have h := splitr (1 : R).
by rewrite !mul1r in h; exact: esym h.
Qed.

(** Source for [norm_half_double]: Federer 2.8.9, p. 146;
    averaging two identical scalar bounds retains that bound. *)
Lemma norm_half_double (R : realFieldType) (a : R) : (2:R)^-1 * (a+a) = a.
Proof. by rewrite mulrDr -mulrDl norm_half_sum_one mul1r. Qed.

(** Source for [inner_norm_strictly_convex]: Federer 2.8.9, p. 146,
    every norm coming from an inner product is strictly convex. The proof
    derives strictness from the earlier proved triangle-equality criterion. *)
Theorem inner_norm_strictly_convex (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (N : V -> R) (hN : is_real_norm N) (hBN : is_inner_norm B N) :
  is_strictly_convex_norm N.
Proof.
move=> x y he hne.
have hy : y != 0.
  apply/eqP=> hy0.
  have hx0 : x = 0 by apply: hN.2; rewrite he hy0 (real_seminorm_zero hN.1).
  by apply: hne; rewrite hx0 hy0.
have hlt : N (x+y) < N x + N y.
  rewrite lt_def; apply/andP; split; last exact: (real_seminorm_triangle hN.1 x y).
  apply/eqP=> hsum.
  have [t [ht hxy]] := @inner_triangle_positive_multiple R V B hB N hN hBN x y hy (esym hsum).
  have hn := congr1 N hxy.
  rewrite (real_seminorm_scale hN.1) (ger0_norm ht) in hn.
  have hny : N y != 0 by rewrite (real_norm_zero_test hN.1 hN.2).
  have ht1 : t = 1.
    apply: (mulIf hny); by rewrite mul1r -hn he.
  by apply: hne; rewrite hxy ht1 scale1r.
have h : (2:R)^-1 * N (x+y) < (2:R)^-1 * (N x + N x).
  by rewrite (ltr_pM2l (@positive_norm_half R)); rewrite -he in hlt.
rewrite norm_half_double in h.
by rewrite /norm_midpoint (real_seminorm_scale hN.1)
  (gtr0_norm (@positive_norm_half R)).
Qed.

(** Source for [canonical_inner_norm_strictly_convex]: Federer 2.8.9,
    p. 146; the actual opaque inner-product norm satisfies the preceding
    independent strict-convexity laws, in every ambient dimension. *)
Theorem canonical_inner_norm_strictly_convex (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) :
  is_strictly_convex_norm (inner_norm hB).
Proof.
have hN : is_real_norm (inner_norm hB).
  split.
  - split; [exact: inner_norm_nonnegative | exact: inner_normZ | exact: inner_norm_triangle].
  - move=> x hx; apply/eqP; by rewrite -(inner_norm_eq0 hB) hx eqxx.
exact: (@inner_norm_strictly_convex R V B hB (inner_norm hB) hN (inner_norm_laws hB)).
Qed.
