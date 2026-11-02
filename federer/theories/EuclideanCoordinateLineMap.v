(** Federer (1969), 3.1.4, p. 214: the two linear epimorphisms
    (x,t) -> x+t e_i and (x,t) -> x used to form the measurable
    coordinate difference quotient. These are the printed explicit maps. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanBlockCoordinates EuclideanOneCoordinate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CoordinateLine.
Variable R : realType.
Variable n : nat.
Local Notation E k := (inner_metric_space (@euclidean_inner_productP R k)).

(** Source for [euclidean_coordinate_parameter_base]: the base-point
    projection used in f(x) of Federer 3.1.4, p. 214. *)
Definition euclidean_coordinate_parameter_base (w : R_n R (n+1)) : R_n R n :=
  (@euclidean_block_split R n 1 w).1.

(** Source for [euclidean_coordinate_parameter_base_linear]: linearity
    of the base projection in the application of 3.1.3(3) in Federer
    3.1.4, p. 214. *)
Lemma euclidean_coordinate_parameter_base_linear : linear euclidean_coordinate_parameter_base.
Proof.
by move=> c x y; apply/ffunP=> j;
  rewrite /euclidean_coordinate_parameter_base /euclidean_block_split !ffunE.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (R_n R (n+1)) (R_n R n) *:%R
  euclidean_coordinate_parameter_base euclidean_coordinate_parameter_base_linear.

(** Source for [euclidean_coordinate_parameter_base_surjective]: the
    base projection is an epimorphism, supporting Federer 3.1.4, p. 214. *)
Lemma euclidean_coordinate_parameter_base_surjective x :
  exists w, euclidean_coordinate_parameter_base w=x.
Proof.
exists (@euclidean_block_join R n 1 (x,0)).
by rewrite /euclidean_coordinate_parameter_base euclidean_block_joinK.
Qed.

Variable i : 'I_n.

(** Source for [euclidean_coordinate_line_map]: the map alpha(x,t)
    = x+t e_i explicitly used in Federer 3.1.4, p. 214. *)
Definition euclidean_coordinate_line_map (w : R_n R (n+1)) : R_n R n :=
  (@euclidean_block_split R n 1 w).1+
  euclidean_one_project (@euclidean_block_split R n 1 w).2*:(@coordinate_basis R n i).

(** Source for [euclidean_coordinate_line_map_linear]: linearity of
    the printed alpha in Federer 3.1.4, p. 214. *)
Lemma euclidean_coordinate_line_map_linear : linear euclidean_coordinate_line_map.
Proof.
move=> c x y; apply/ffunP=> j.
rewrite /euclidean_coordinate_line_map /euclidean_one_project /euclidean_block_split /= !ffunE.
by rewrite scalerDl scalerDr scalerA addrACA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (R_n R (n+1)) (R_n R n) *:%R
  euclidean_coordinate_line_map euclidean_coordinate_line_map_linear.

(** Source for [euclidean_coordinate_line_map_surjective]: the
    surjectivity needed to apply 3.1.3(3) in Federer 3.1.4, p. 214;
    the pair (x,0) maps to x. *)
Lemma euclidean_coordinate_line_map_surjective x : exists w, euclidean_coordinate_line_map w=x.
Proof.
exists (@euclidean_block_join R n 1 (x,0)).
by rewrite /euclidean_coordinate_line_map euclidean_block_joinK /euclidean_one_project ffunE scale0r addr0.
Qed.

(** Source for [euclidean_coordinate_line_map_pair]: evaluation in
    block coordinates of the printed map in Federer 3.1.4, p. 214. *)
Lemma euclidean_coordinate_line_map_pair x t :
  euclidean_coordinate_line_map (@euclidean_block_join R n 1 (x,t))=
  x+euclidean_one_project t*:(@coordinate_basis R n i).
Proof. by rewrite /euclidean_coordinate_line_map euclidean_block_joinK. Qed.
End CoordinateLine.
