(** Federer (1969), 3.2.48, p. 285: left translation
    carries the actual horizontal lift at the identity
    to the actual lift at g. Supporting commutation of
    the tangent-coordinate diagram, using public adjoint laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalMaps EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  SphericalHorizontalLift.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_horizontal_lift_left_translate]: supporting
    the first vertical arrow in the actual differential
    diagram of 3.2.48, p. 285. This equality
    holds for every original vector v, before imposing
    tangent membership or choosing any tangent frame. *)
Lemma spherical_horizontal_lift_left_translate (R:realType) N
    (g:Hom (R_n R N) (R_n R N)) (c v:R_n R N):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  spherical_horizontal_lift g c (g v)=
    hom_comp g (spherical_horizontal_lift (hom_of_linear (linear_id (R_n R N))) c v).
Proof.
move=>hg.
pose identity:Hom (R_n R N) (R_n R N):=hom_of_linear (linear_id (R_n R N)).
have hId:is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear identity) by move=>x y.
have hAdjointId x:euclidean_rectangular_adjoint identity x=x.
  exact (@euclidean_orthogonal_adjoint_cancel R N identity hId x).
apply:hom_ext=>x.
change (euclidean_inner_product x c*:(g v)-
  euclidean_inner_product x (euclidean_rectangular_adjoint g (g v))*:g c=
  g (euclidean_inner_product x c*:v-
    euclidean_inner_product x (euclidean_rectangular_adjoint identity v)*:c)).
by rewrite (euclidean_orthogonal_adjoint_cancel hg) hAdjointId linearB !linearZ.
Qed.
