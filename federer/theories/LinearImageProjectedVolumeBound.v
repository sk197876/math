(** Supporting Federer (1969), 3.2.45, p. 279: reduce an
    arbitrary linear image volume to an actual orthogonal projection
    by the earlier polar and determinant laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  CoordinateProjection PolarFactorisationUP PolarProjection EuclideanNormalJacobian
  EuclideanLebesgueDimensions EuclideanLebesgueDeterminant ProjectedVolumeGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [linear_image_projected_volume_bound]: an expanded
    helper for the continuity assertion of Federer 3.2.45, p. 279.
    Apply the polar projection factorization of 1.7.3, p. 30,
    the determinant transport of 2.7.16, p. 134, and the original
    projected-volume supremum of 2.10.4, p. 172. Singular maps,
    arbitrary source sets and every admissible natural degree remain. *)
Theorem linear_image_projected_volume_bound (R : realType) n m
    (F : {linear R_n R n -> R_n R m})
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (m <= n)%N ->
  @euclidean_lebesgue_measure R m (F @` S) <=
    (euclidean_normal_jacobian F)%:E * @projected_volume_gauge R n m S.
Proof.
move=> hMN.
have [K [p hFactor]] := @polar_projection_factorisation_exists R (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m) hMN F.
have hImage : F @` S = K @` (p @` S).
  apply/seteqP; split=> y.
  - move=> [x hx <-]; exists (p x); last exact: projection_factor_equation hFactor x.
    by exists x.
  - move=> [z [x hx <-] <-]; exists x=> //; symmetry; exact: projection_factor_equation hFactor x.
rewrite hImage euclidean_lebesgue_linear_image -(projection_factor_normal_jacobian hFactor).
apply: lee_wpmul2l; first by rewrite lee_fin; exact: euclidean_normal_jacobian_nonnegative.
apply: projected_volume_gauge_projection_bound.
exact: (O_star_projection p).2 (projection_factor_orthogonal hFactor).
Qed.
