(** Federer (1969), 4.1.11, p. 366: the
    original Cartesian product of two affine maps is
    affine. Reuse the original block projections, block
    joining and affine-map laws from 2.7.16, p. 133,
    for the arbitrary-ambient prism transfer. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear AffineMaps GrassmannAbbreviations
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps EuclideanCartesianMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_cartesian_affine_map]: the original
    product affine map used to send the standard
    simplicial prism to its arbitrary prescribed segment
    and simplex factors, supporting Federer 4.1.11,
    p. 366. Singular maps and empty blocks are allowed. *)
Theorem current_cartesian_affine_map (R:realType) m mu n nu
    (f:R_n R m->R_n R n) (g:R_n R mu->R_n R nu):
  is_affine_map f->is_affine_map g->is_affine_map (@euclidean_cartesian_map R m mu n nu f g).
Proof.
move=>hf hg x y a b hab.
pose p:=@euclidean_first_block_map R m mu.
pose q:=@euclidean_last_block_map R m mu.
change (@euclidean_block_join R n nu
    (f (p (a*:x+b*:y)),g (q (a*:x+b*:y)))=
  a*:@euclidean_block_join R n nu (f (p x),g (q x))+
  b*:@euclidean_block_join R n nu (f (p y),g (q y))).
rewrite (hom_linear p a x (b*:y)) (linZ (hom_linear p) b y)
  (hom_linear q a x (b*:y)) (linZ (hom_linear q) b y)
  (hf (p x) (p y) a b hab) (hg (q x) (q y) a b hab).
change (@euclidean_block_join R n nu
    (a*:(f (p x),g (q x))+b*:(f (p y),g (q y)))=
  a*:@euclidean_block_join R n nu (f (p x),g (q x))+
  b*:@euclidean_block_join R n nu (f (p y),g (q y))).
rewrite (@euclidean_block_join_linear R n nu a (f (p x),g (q x))
  (b*:(f (p y),g (q y)))).
by rewrite (linZ (@euclidean_block_join_linear R n nu) b (f (p y),g (q y))).
Qed.
