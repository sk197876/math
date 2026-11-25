(** Federer (1969), 2.10.46, printed p. 203: for f in O*(m+n,m+k), there are
    p in O*(m+k,k) and q in O*(n,k) such that p(f(x,y))=q(y). This is
    exactly the application of the final paragraph of 1.7.4, p. 31, to f and
    the second-coordinate projection. The already proved common-factor
    theorem supplies existence; no choice of factors is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockCoordinates CoordinateProjection CommonProjectionFactor EuclideanRightBlockProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_product_projection_factor]: direct
    common-factor observation in 2.10.46, p. 203,
    including zero dimensions. The result quantifies over
    supplied orthogonal projections, so no additional
    dimension hypothesis is needed when that family is empty. *)
Theorem euclidean_product_projection_factor (R : realType) m n k
    (f : {linear R_n R (m+n) -> R_n R (m+k)}) :
  O_star f -> exists (p : {linear R_n R (m+k) -> R_n R k})
    (q : {linear R_n R n -> R_n R k}),
    O_star p /\ O_star q /\ forall x y,
      p (f (@euclidean_block_join R m n (x,y)))=q y.
Proof.
move=> hf.
pose g := GRing.Linear.clone _ _ _ _ (@euclidean_right_block R m n) _.
have hg := @euclidean_right_block_orthogonal_projection R m n.
have hdim : ((m+n)+k<=(m+k)+n)%N by rewrite addnAC.
have [p [q [hp [hq he]]]] := @common_orthogonal_projection_factor R
  (R_n R (m+n)) (R_n R (m+k)) (R_n R n) (R_n R k)
  (@euclidean_inner_product R (m+n)) (@euclidean_inner_product R (m+k))
  (@euclidean_inner_product R n) (@euclidean_inner_product R k)
  (@euclidean_inner_productP R (m+n)) (@euclidean_inner_productP R (m+k))
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R k)
  (m+n) (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n))
  (m+k) (@coordinate_basis R (m+k)) (@coordinate_basisP R (m+k))
  n (@coordinate_basis R n) (@coordinate_basisP R n)
  k (@coordinate_basis R k) (@coordinate_basisP R k)
  f g ((O_star_projection f).1 hf) ((O_star_projection g).1 hg) hdim.
exists p,q; split; first exact: (O_star_projection p).2 hp.
split; first exact: (O_star_projection q).2 hq.
move=> x y; have hh := he (@euclidean_block_join R m n (x,y)).
by rewrite /g /= euclidean_right_block_pair in hh.
Qed.
