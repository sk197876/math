(** Federer (1969), 2.6.6, pp. 120–121: a compact Hausdorff inverse limit
    and its projections. This abstract specification uses continuous
    compatible projections, separation of points, and unique realization of
    every compatible coordinate family. Compactness and Hausdorff separation
    determine the limit topology from these maps. No concrete subspace is
    exposed in the downstream integration statements. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compatible_inverse_family]: the coordinate
    compatibility equations defining an inverse limit in the final
    paragraph of Federer 2.6.6, pp. 120–121. *)
Definition compatible_inverse_family (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i) (u : prod_topology Y) :=
  forall i j, le i j -> b i j (u j)=u i.

(** Source for [is_compact_inverse_limit]: abstract compact
    Hausdorff limit laws for Federer 2.6.6, pp. 120–121.
    Uniqueness of realization follows from point separation. *)
Record is_compact_inverse_limit (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i)
    (X : topologicalType) (p : forall i, X -> Y i) : Prop := {
  (** Source for [compact_inverse_limit_compact]: compactness
      of the limit, supporting Federer 2.6.6, pp. 120–121. *)
  compact_inverse_limit_compact : compact (@setT X);
  (** Source for [compact_inverse_limit_hausdorff]: Hausdorff
      separation of the limit, supporting Federer 2.6.6, pp. 120–121. *)
  compact_inverse_limit_hausdorff : hausdorff_space X;
  (** Source for [compact_inverse_limit_projection_continuous]:
      continuous projections, supporting Federer 2.6.6, pp. 120–121. *)
  compact_inverse_limit_projection_continuous : forall i, continuous (p i);
  (** Source for [compact_inverse_limit_projection_compatible]:
      compatibility of projections, supporting Federer 2.6.6,
      pp. 120–121. *)
  compact_inverse_limit_projection_compatible : forall x i j, le i j -> b i j (p j x)=p i x;
  (** Source for [compact_inverse_limit_realizes_family]: every
      compatible coordinate family is realized by a limit point,
      supporting Federer 2.6.6, pp. 120–121. *)
  compact_inverse_limit_realizes_family : forall u, compatible_inverse_family le b u ->
    exists x, forall i, p i x=u i;
  (** Source for [compact_inverse_limit_separates]: the projections
      separate points, giving uniqueness of realization in Federer
      2.6.6, pp. 120–121. *)
  compact_inverse_limit_separates : forall x y, (forall i, p i x=p i y) -> x=y
}.
