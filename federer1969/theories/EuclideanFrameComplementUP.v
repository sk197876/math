(** Federer (1969), 3.2.28(2)–(3), printed pp. 264–266:
    normal directions to an orthogonal frame. The linear maps
    below are specified by their orthogonality, cancellation
    and exact normal-range laws. Existence is proved separately
    from the sealed orthogonal projection charts of 1.7.4. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalMaps EuclideanRectangularAdjoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_euclidean_frame_complement]: independent
    orthogonal-complement coordinate laws supporting Z(g) and
    the adapted tangent bases in Federer 3.2.28(2)–(3),
    pp. 264–266, through 1.7.3–1.7.4, pp. 30–31.
    This specification introduces no unproved existence axiom. *)
Record is_euclidean_frame_complement (R:realType) m n k
    (g:Hom (R_n R m) (R_n R n))
    (a:Hom (R_n R k) (R_n R n)) (p:Hom (R_n R n) (R_n R k)):Prop:={
  (** Source for [frame_complement_orthogonal]: the normal
      frame is orthonormal, supporting Federer 3.2.28,
      pp. 264–266, by 1.7.3, p. 30. *)
  frame_complement_orthogonal:is_orthogonal_map (@euclidean_inner_product R k)
    (@euclidean_inner_product R n) (hom_as_linear a);
  (** Source for [frame_complement_cancel]: exact normal
      coordinates, supporting Federer 3.2.28, pp. 264–266,
      by 1.7.4, pp. 30–31. *)
  frame_complement_cancel:cancel a p;
  (** Source for [frame_complement_normal]: all normal
      coordinate vectors are orthogonal to g, supporting
      Z(g) in Federer 3.2.28(2), p. 264. *)
  frame_complement_normal:forall u,euclidean_rectangular_adjoint g (a u)=0;
  (** Source for [frame_complement_range]: the normal
      coordinates exhaust the exact orthogonal complement,
      supporting dim Z(g) in Federer 3.2.28(2), p. 264. *)
  frame_complement_range:forall x,euclidean_rectangular_adjoint g x=0 ->a (p x)=x
}.
