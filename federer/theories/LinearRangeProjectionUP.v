(** Federer (1969), 3.1.18, p. 229: abstract orthogonal range
    projection laws. Their existence is proved separately in
    LinearRangeProjection.v using the public sealed adjoint. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct OrthogonalMaps AdjointUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_linear_range_projection]: abstract laws of p and
    its adjoint p* in Federer 3.1.18, p. 229. The injection is
    orthogonal, p is its adjoint, and its image is exactly the range of L. *)
Record is_linear_range_projection (R:realType) (X Y:lmodType R)
    (C:Y->Y->R) (L:Hom X Y) v
    (p:{linear Y->R_n R v}) (j:{linear R_n R v->Y}) : Prop := {
  (** Source for [range_projection_orthogonal]: p* is an orthogonal
      injection, Federer 3.1.18, p. 229, using 1.7.2. *)
  range_projection_orthogonal : is_orthogonal_map (@euclidean_inner_product R v) C j;
  (** Source for [range_projection_adjoint]: p is the adjoint of the
      orthogonal injection, Federer 3.1.18, p. 229, using 1.7.4. *)
  range_projection_adjoint : is_adjoint (@euclidean_inner_product R v) C j p;
  (** Source for [range_projection_cancel]: p p*=identity, supporting
      the projections in Federer 3.1.18, pp. 229–230. *)
  range_projection_cancel : cancel j p;
  (** Source for [range_projection_image]: image p*=image L,
      the prescribed projection in Federer 3.1.18, p. 229. *)
  range_projection_image : forall y, (exists u, j u=y) <-> (exists x, L x=y)
}.
