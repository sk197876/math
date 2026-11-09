(** Federer (1969), 3.3.4, pp. 288–289: the
    first m coordinates of an orthogonal frame define
    the actual projection whose kernel is v(g).
    Here the coordinate splitting R^(m+k) keeps the
    positive normal block explicit, without truncation. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  EuclideanBlockCoordinates EuclideanBlockLinear EuclideanBlockLinearMaps
  EuclideanBlockProjection CoordinateProjection AdjointUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [structure_first_block_projection]: the
    coordinate projection onto the first m frame
    coordinates, supporting v(g) in Federer 3.3.4,
    pp. 288–289. This is the actual map in
    O*(m+k,m), not a supplied projection witness. *)
Definition structure_first_block_projection (R:realType) m k:
    {linear R_n R (m+k)->R_n R m}:=
  hom_as_linear (@euclidean_first_block_map R m k).

(** Source for [structure_first_block_projection_orthogonal]:
    the first-coordinate map belongs to O*(m+k,m),
    supporting Federer 3.3.4, p. 289, by the
    actual block inclusion as its orthogonal adjoint. *)
Theorem structure_first_block_projection_orthogonal (R:realType) m k:
  O_star (@structure_first_block_projection R m k).
Proof.
pose f:{linear R_n R m->R_n R (m+k)}:=
  hom_as_linear (@euclidean_first_injection_map R m k).
exists f; split.
- move=>x y.
  change (euclidean_inner_product (@euclidean_first_injection R m k x)
    (@euclidean_first_injection R m k y)=euclidean_inner_product x y).
  rewrite /euclidean_first_injection euclidean_block_join_inner /=.
  by rewrite (bil0l (inner_bilinear (@euclidean_inner_productP R k))) addr0.
- move=>x y.
  change (euclidean_inner_product x (@euclidean_first_block R m k y)=
    euclidean_inner_product (@euclidean_first_injection R m k x) y).
  rewrite (@euclidean_block_split_inner R m k).
  have hFirst:=@euclidean_first_block_injectionK R m k x.
  have hLast:=@euclidean_last_block_first_injection R m k x.
  change (euclidean_inner_product x (@euclidean_first_block R m k y)=
    euclidean_inner_product (@euclidean_first_block R m k (@euclidean_first_injection R m k x))
      (@euclidean_first_block R m k y)+
    euclidean_inner_product (@euclidean_last_block R m k (@euclidean_first_injection R m k x))
      (@euclidean_last_block R m k y)).
  by rewrite hFirst hLast (bil0l (inner_bilinear (@euclidean_inner_productP R k))) addr0.
Qed.
