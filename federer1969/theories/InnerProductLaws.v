(** Federer (1969), 1.7.1, p. 28: elementary consequences of the
    inner-product laws, used in the norm and orthogonality arguments. Source
    editions and erratum convention: InnerProductUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Laws.
Variable R : realFieldType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation hb := (inner_bilinear hB).

(** Source for [inner_nonnegative]: Federer 1.7.1, p. 28,
    the nonnegative quadratic expression. Every diagonal value is
    nonnegative, including the zero vector. *)
Lemma inner_nonnegative x : 0 <= B x x.
Proof.
case hx: (x == 0); first by move/eqP: hx => ->; rewrite (bil0l hb).
apply: ltW; by rewrite (inner_positive hB) hx.
Qed.

(** Source for [inner_self_eq0]: Federer 1.7.1, p. 28,
    definiteness. A diagonal value vanishes exactly at the zero vector. *)
Lemma inner_self_eq0 x : (B x x == 0) = (x == 0).
Proof.
case hx: (x == 0); first by move/eqP: hx => ->; rewrite (bil0l hb) eqxx.
apply/negP=> /eqP hz.
have hp : 0 < B x x by rewrite (inner_positive hB) hx.
by rewrite hz ltxx in hp.
Qed.

(** Source for [inner_left_separates]: Federer 1.7.1, pp. 27-28,
    the associated polarity is injective. Supporting nondegeneracy:
    a vector orthogonal to every vector must be zero. *)
Lemma inner_left_separates x : (forall y, B x y = 0) -> x = 0.
Proof. move=> h; apply/eqP; by rewrite -inner_self_eq0 h eqxx. Qed.

(** Source for [inner_right_separates]: Federer 1.7.1, pp. 27-28,
    nondegeneracy in the second argument, by symmetry. *)
Lemma inner_right_separates y : (forall x, B x y = 0) -> y = 0.
Proof. move=> h; apply: inner_left_separates => x; by rewrite (inner_symmetric hB) h. Qed.

(** Source for [inner_scale_square]: Federer 1.7.1, p. 28,
    the quadratic expression: B(a x,a x)=a^2 B(x,x). *)
Lemma inner_scale_square a x : B (a *: x) (a *: x) = a ^+ 2 * B x x.
Proof.
rewrite (bilZl hb) (bilZr hb) /=.
change (a * (a * B x x) = a ^+ 2 * B x x).
by rewrite mulrA -expr2.
Qed.

(** Source for [inner_sum_square]: Federer 1.7.1, p. 28,
    expansion of the diagonal quadratic form at x+y. *)
Lemma inner_sum_square x y :
  B (x+y) (x+y) = B x x + (B x y + B x y) + B y y.
Proof.
rewrite (bilDl hb) ! (bilDr hb) (inner_symmetric hB y x).
by rewrite !addrA.
Qed.

(** Source for [inner_quadratic_expansion]: Federer 1.7.1,
    p. 28, displayed identity t^2(x.x)+2t(x.y)+(y.y)
    =(t x+y).(t x+y), the starting point of Cauchy's inequality. *)
Lemma inner_quadratic_expansion t x y :
  B (t *: x+y) (t *: x+y) =
  t ^+ 2 * B x x + (2 * t) * B x y + B y y.
Proof.
rewrite inner_sum_square inner_scale_square (bilZl hb) /=.
change (t ^+ 2 * B x x + (t * B x y + t * B x y) + B y y =
  t ^+ 2 * B x x + (2 * t) * B x y + B y y).
by rewrite mulr_natl mulr2n mulrDl.
Qed.
End Laws.
