(** Federer (1969), 3.1.19, p. 231: linear coordinates adapted
    to the plane Z in a straightening chart. Existence is proved
    separately from this specification, using 1.6.1 and 1.6.3. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanBlockLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_subspace_block_chart]: supporting (1) implies
    (2) and (4) in Federer 3.1.19, p. 231. Invertible linear
    coordinates turn a mu-plane into the zero set of the remaining
    coordinates. The specification makes no construction choices. *)
Record is_subspace_block_chart (R:realType) mu l
    (Z:subspace (R_n R (mu+l))) (beta gamma:Hom (R_n R (mu+l)) (R_n R (mu+l))) : Prop := {
  (** Source for [subspace_chart_forward_inverse]: the forward
      coordinate inverse law supporting 3.1.19, p. 231. *)
  subspace_chart_forward_inverse : cancel beta gamma;
  (** Source for [subspace_chart_backward_inverse]: the reverse
      coordinate inverse law supporting 3.1.19, p. 231. *)
  subspace_chart_backward_inverse : cancel gamma beta;
  (** Source for [subspace_chart_plane]: the exact zero set of
      the complementary coordinates, supporting 3.1.19, p. 231. *)
  subspace_chart_plane : forall x, Z x <-> @euclidean_last_block_map R mu l (beta x)=0
}.
