(** Federer (1969), 3.2.46, p. 281: the straight
    segment between points of the frozen ellipsoid stays
    in that ellipsoid. This supporting convexity proof uses
    only linearity and the ordinary norm triangle inequality. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerNormInequalities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_ellipsoid_segment_bound]: straight
    segments stay inside the L-coordinate comparison region of
    Federer 3.2.46, p. 281. L may be singular in this supporting
    convexity assertion; zero radius and all dimensions remain. *)
Lemma euclidean_ellipsoid_segment_bound (R : realType) n
    (L : {linear R_n R n -> R_n R n}) a x y (r t : R) :
  inner_norm (@euclidean_inner_productP R n) (L (x-a)) <= r ->
  inner_norm (@euclidean_inner_productP R n) (L (y-a)) <= r ->
  0 <= t <= 1 ->
  inner_norm (@euclidean_inner_productP R n) (L ((x+t*:(y-x))-a)) <= r.
Proof.
move=> hx hy /andP [ht ht1].
have hVec : (x+t*:(y-x))-a = (1-t)*:(x-a)+t*:(y-a).
  apply/ffunP=> i; rewrite !ffunE.
  change (x i+t*(y i-x i)-a i = (1-t)*(x i-a i)+t*(y i-a i)); ring.
rewrite hVec linearD !linearZ.
have ht' : 0 <= 1-t by rewrite subr_ge0.
have h := inner_norm_triangle (@euclidean_inner_productP R n)
  ((1-t)*:L (x-a)) (t*:L (y-a)).
rewrite !inner_normZ (ger0_norm ht') (ger0_norm ht) in h.
have hUpper := le_trans h (lerD (ler_wpM2l ht' hx) (ler_wpM2l ht hy)).
have hRadius : (1-t)*r+t*r=r by ring.
by rewrite hRadius in hUpper.
Qed.
