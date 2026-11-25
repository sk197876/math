(** Actual diagonal inverse and Minkowski-sum transport
    supporting Federer (1969), 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanLinearMaps VectorSetSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [linear_vector_set_sum_image]: supporting
    linear transport of the original tube sums in Federer
    3.2.45, pp. 279–280. The image of the
    actual pairwise sum is the sum of the two
    images, by additivity. No injectivity, boundedness
    or nonemptiness premise is imposed. *)
Lemma linear_vector_set_sum_image (R : pzRingType) (V W : lmodType R)
    (F : {linear V -> W}) (A B : set V) :
  F @` vector_set_sum A B=vector_set_sum (F @` A) (F @` B).
Proof.
apply/seteqP; split=> z.
- move=> [x /vector_set_sum_membership [a [b [ha [hb ->]]]] <-].
  rewrite linearD; apply: vector_set_sum_contains.
  + by exists a.
  + by exists b.
- move=> /vector_set_sum_membership [x [y [[a ha <-] [[b hb <-] ->]]]].
  exists (a+b); first exact: vector_set_sum_contains ha hb.
  by rewrite linearD.
Qed.

(** Source for [euclidean_prefix_stretch_inverse]: supporting
    exact nonzero diagonal change of variables in Federer
    3.2.45, pp. 279–280. Scaling the first m
    coordinates by h and then by its actual scalar
    inverse returns the original point. The formula
    retains an empty first block and ambient zero. *)
Lemma euclidean_prefix_stretch_inverse (R : realType) n m (h : R) :
  h!=0 -> cancel
    (@euclidean_diagonal_map R n (fun j => if (j<m)%N then h^-1 else 1))
    (@euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1)).
Proof.
move=> hh x; apply/ffunP=> j; rewrite /euclidean_diagonal_map /euclidean_diagonal !ffunE.
case: (j<m)%N; last by rewrite !mul1r.
by rewrite mulrA mulfV // mul1r.
Qed.

(** Source for [euclidean_prefix_inverse_sum_image]: supporting
    anisotropic tube normalization in Federer 3.2.45,
    pp. 279–280. The exact image of the tube
    around the inverse-stretched K is the original K
    plus the compressed ball. This statement retains
    the actual original sets and uses only the
    proved diagonal inverse and additive image laws. *)
Theorem euclidean_prefix_inverse_sum_image (R : realType) n m (h : R)
    (K B : set (R_n R n)) :
  h!=0 ->
  (@euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1)) @`
    vector_set_sum ((@euclidean_diagonal_map R n (fun j => if (j<m)%N then h^-1 else 1)) @` K) B=
  vector_set_sum K ((@euclidean_diagonal_map R n (fun j => if (j<m)%N then h else 1)) @` B).
Proof.
move=> hh; rewrite linear_vector_set_sum_image; congr (vector_set_sum _ _).
apply/seteqP; split.
- move=> x [y [z hz <-] <-]; by rewrite euclidean_prefix_stretch_inverse.
- move=> x hx; exists (@euclidean_diagonal_map R n (fun j => if (j<m)%N then h^-1 else 1) x).
  + by exists x.
  + exact: euclidean_prefix_stretch_inverse hh x.
Qed.
