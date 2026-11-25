(** Federer (1969), 3.2.28(3), printed p. 265:
    the last adapted source basis vector is a unit normal
    to im alpha, where alpha is in O(m,m-1).
    Specify the normal line before proving its existence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  EuclideanRectangularAdjoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_euclidean_hyperplane_normal]: the adapted
    vector e_m perpendicular to im alpha in Federer
    3.2.28(3), p. 265. The norm, normality and
    exact normal-line spanning law are independent
    obligations; no vector is postulated to exist. *)
Record is_euclidean_hyperplane_normal (R:realType) k
    (alpha:Hom (R_n R k) (R_n R k.+1)) (w:R_n R k.+1):Prop:={
  (** Source for [hyperplane_normal_unit]: the last
      adapted vector has squared length one, Federer
      3.2.28(3), p. 265. *)
  hyperplane_normal_unit:euclidean_inner_product w w= 1;
  (** Source for [hyperplane_normal_perpendicular]: this
      vector is perpendicular to im alpha, Federer
      3.2.28(3), p. 265. *)
  hyperplane_normal_perpendicular:euclidean_rectangular_adjoint alpha w=0;
  (** Source for [hyperplane_normal_span]: the orthogonal
      complement is the line through the last basis vector,
      supporting the fibre computation of Federer
      3.2.28(3), pp. 265–266. *)
  hyperplane_normal_span:forall z,euclidean_rectangular_adjoint alpha z=0 ->
    z=euclidean_inner_product z w*:w
}.
