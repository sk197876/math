(** Federer (1969), 2.10.46, p. 204: supporting block projections for the
    lower Gross product inequality. Extend a projection q on the second
    factor by the identity on the first. Its adjoint and orthogonality
    follow from 1.7.4, pp. 30–31, in the block coordinates of 2.6.5, p. 120. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanBlockLinear CoordinateProjection AdjointUP MetricProductRectangles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_block_projection]: supporting map
    (x,y) maps to (x,q(y)) for the opposite inequality
    asserted in 2.10.46, p. 204. This is the
    specified coordinate map, not a selected existence witness. *)
Definition euclidean_block_projection (R : realType) m n k
    (q : {linear R_n R n -> R_n R k}) (z : R_n R (m+n)) : R_n R (m+k) :=
  @euclidean_block_join R m k ((@euclidean_block_split R m n z).1,
    q (@euclidean_block_split R m n z).2).

(** Source for [euclidean_block_projection_linear]: supporting
    linearity of the block map used in 2.10.46, p. 204. *)
Lemma euclidean_block_projection_linear (R : realType) m n k
    (q : {linear R_n R n -> R_n R k}) :
  linear (@euclidean_block_projection R m n k q).
Proof.
move=> a x y.
have hs : @euclidean_block_split R m n (a*:x+y)=
    a*:(@euclidean_block_split R m n x)+(@euclidean_block_split R m n y).
  by congr (_, _); apply/ffunP=> i; rewrite /euclidean_block_split !ffunE.
rewrite /euclidean_block_projection hs /= linearP.
exact (@euclidean_block_join_linear R m k a
  ((@euclidean_block_split R m n x).1,q (@euclidean_block_split R m n x).2)
  ((@euclidean_block_split R m n y).1,q (@euclidean_block_split R m n y).2)).
Qed.
HB.instance Definition _ (R : realType) m n k (q : {linear R_n R n -> R_n R k}) :=
  GRing.isLinear.Build R (R_n R (m+n)) (R_n R (m+k)) *:%R
    (@euclidean_block_projection R m n k q) (@euclidean_block_projection_linear R m n k q).

(** Source for [euclidean_block_projection_pair]: supporting
    coordinate evaluation for the rectangle projection in
    2.10.46, p. 204. *)
Lemma euclidean_block_projection_pair (R : realType) m n k
    (q : {linear R_n R n -> R_n R k}) (x : R_n R m) (y : R_n R n) :
  euclidean_block_projection q (@euclidean_block_join R m n (x,y))=
    @euclidean_block_join R m k (x,q y).
Proof. by rewrite /euclidean_block_projection euclidean_block_joinK. Qed.

(** Source for [euclidean_block_split_inner]: supporting inner
    product decomposition in the block coordinates of 2.6.5,
    p. 120, used for the projection adjoint in 2.10.46,
    p. 204. This is the inverse form of the join law. *)
Lemma euclidean_block_split_inner (R : realType) m n (x y : R_n R (m+n)) :
  euclidean_inner_product x y=
    euclidean_inner_product (@euclidean_block_split R m n x).1 (@euclidean_block_split R m n y).1+
    euclidean_inner_product (@euclidean_block_split R m n x).2 (@euclidean_block_split R m n y).2.
Proof.
have he := @euclidean_block_join_inner R m n
  (@euclidean_block_split R m n x) (@euclidean_block_split R m n y).
by rewrite !euclidean_block_splitK in he.
Qed.

(** Source for [euclidean_block_projection_orthogonal]: supporting
    O*(m+n,m+k) membership of the block projection used
    for the Gross lower bound in 2.10.46, p. 204.
    The adjoint is the block map of the given adjoint. *)
Theorem euclidean_block_projection_orthogonal (R : realType) m n k
    (q : {linear R_n R n -> R_n R k}) :
  O_star q -> O_star (GRing.Linear.clone _ _ _ _ (@euclidean_block_projection R m n k q) _).
Proof.
move=> [h [hh hadj]].
exists (GRing.Linear.clone _ _ _ _ (@euclidean_block_projection R m k n h) _); split.
- move=> x y; rewrite /euclidean_block_projection euclidean_block_join_inner /= hh.
  have he := @euclidean_block_join_inner R m k
    (@euclidean_block_split R m k x) (@euclidean_block_split R m k y).
  rewrite !euclidean_block_splitK in he; exact: esym he.
- move=> x y.
  change (euclidean_inner_product x (@euclidean_block_projection R m n k q y)=
    euclidean_inner_product (@euclidean_block_projection R m k n h x) y).
  rewrite (@euclidean_block_split_inner R m k x _)
    (@euclidean_block_split_inner R m n _ y).
  by rewrite /euclidean_block_projection !euclidean_block_joinK /= hadj.
Qed.

(** Source for [euclidean_block_projection_rectangle]: supporting
    image identity used to compare projected volumes in
    2.10.46, p. 204. No measurability or nonemptiness
    assumption is required for this set identity. *)
Lemma euclidean_block_projection_rectangle (R : realType) m n k
    (q : {linear R_n R n -> R_n R k}) (U : set (R_n R m)) (V : set (R_n R n)) :
  (@euclidean_block_projection R m n k q) @`
    (metric_product_rectangle (fun z=>(@euclidean_block_split R m n z).1)
      (fun z=>(@euclidean_block_split R m n z).2) U V)=
    metric_product_rectangle (fun z=>(@euclidean_block_split R m k z).1)
      (fun z=>(@euclidean_block_split R m k z).2) U (q @` V).
Proof.
apply/seteqP; split.
- move=> z [w [hwU hwV] <-].
  change (U ((@euclidean_block_split R m k (@euclidean_block_projection R m n k q w)).1) /\
    (q @` V) ((@euclidean_block_split R m k (@euclidean_block_projection R m n k q w)).2)).
  rewrite /euclidean_block_projection euclidean_block_joinK /=.
  split=> //; by exists ((@euclidean_block_split R m n w).2).
- move=> z [hzU [y hy hq]].
  exists (@euclidean_block_join R m n ((@euclidean_block_split R m k z).1,y)).
  + change (U ((@euclidean_block_split R m n (@euclidean_block_join R m n
      ((@euclidean_block_split R m k z).1,y))).1) /\
      V ((@euclidean_block_split R m n (@euclidean_block_join R m n
      ((@euclidean_block_split R m k z).1,y))).2)).
    by rewrite euclidean_block_joinK.
  + by rewrite euclidean_block_projection_pair hq euclidean_block_splitK.
Qed.
