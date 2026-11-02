(** Private existence witness supporting Federer (1969), 2.10.46, p. 204,
    and Freilich (1950), Theorem 4.5, Parts 6–7, pp. 247–250. Join and split
    the existing coordinate blocks to implement the abstract law. Source
    context and coordinate convention: EuclideanBlockExtensionUP.v.
    Downstream proofs use the opaque interface, not this implementation. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanBlockCoordinates EuclideanBlockLinear
  EuclideanBlockExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_block_extension_exists]: proved existence
    for the abstract block action supporting 2.10.46, p. 204;
    Freilich (1950), Part 6, pp. 247–249. Both
    blocks may be empty; no extra algebraic assumptions are imposed. *)
Theorem euclidean_block_extension_exists (R : realType) m n
    (h : {linear R_n R n -> R_n R n}) :
  exists H : {linear R_n R (m+n) -> R_n R (m+n)}, is_euclidean_block_extension h H.
Proof.
pose c z := @euclidean_block_join R m n
  ((@euclidean_block_split R m n z).1,h (@euclidean_block_split R m n z).2).
have hs : linear (@euclidean_block_split R m n).
  move=> t x y; rewrite /euclidean_block_split /=.
  congr (_, _); apply/ffunP=> i; by rewrite !ffunE.
have hc : linear c.
  move=> t x y; rewrite /c (hs t x y) /= linearP.
  exact: (@euclidean_block_join_linear R m n t
    ((euclidean_block_split x).1,h (euclidean_block_split x).2)
    ((euclidean_block_split y).1,h (euclidean_block_split y).2)).
pose mix := GRing.isLinear.Build R (R_n R (m+n)) (R_n R (m+n)) *:%R c hc.
pose H : {linear R_n R (m+n) -> R_n R (m+n)} := HB.pack c mix.
exists H=> u y.
change (@euclidean_block_join R m n
  ((@euclidean_block_split R m n (@euclidean_block_join R m n (u,y))).1,
   h (@euclidean_block_split R m n (@euclidean_block_join R m n (u,y))).2)=
  @euclidean_block_join R m n (u,h y)).
by rewrite euclidean_block_joinK.
Qed.
