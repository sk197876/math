(** Federer (1969), 3.2.22, p. 259: when
    the middle space has dimension mu, its top exterior
    map scales every vector by the same volume factor.
    This gives the exact target-chart Jacobian product. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerExterior InnerExteriorPositivity ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorNorm
  ExteriorOperatorNorm OperatorNormUP OperatorNormLaws EuclideanLinearMaps
  EuclideanLinearJacobian EuclideanTopExteriorVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_top_middle_exterior_scale]: the
    target-chart exterior comparison in Federer 3.2.22,
    p. 259. The source of Dgamma is R^mu,
    so 1.7.6 scales each intermediate mu-vector by
    J_mu Dgamma, even when that vector is zero. *)
Lemma euclidean_top_middle_exterior_scale (R:realType) m mu n
    (L:Hom (R_n R m) (R_n R mu)) (D:Hom (R_n R mu) (R_n R n))
    (x:exterior_power (R_n R m) mu):
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (exterior_power_map (hom_as_linear (hom_comp D L)) mu x)=
  euclidean_linear_jacobian mu D*
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R mu)
      (exterior_power_map (hom_as_linear L) mu x).
Proof.
have hComp:hom_as_linear (hom_comp D L)=1 linear_comp (hom_as_linear D) (hom_as_linear L).
  by move=>v.
rewrite (exterior_power_map_ext hComp x) -exterior_power_map_composition.
exact:(euclidean_top_exterior_volume_scale D _).
Qed.

(** Source for [euclidean_top_middle_jacobian_compose]: the
    target-chart comparison in Federer 3.2.22, p. 259,
    follows from the exact identity J_mu(Dgamma composed
    Dphi)=J_mu(Dgamma) J_mu(Dphi). Both norm inequalities
    follow from their abstract unit-ball and attainment laws;
    no injectivity or positive middle dimension is assumed. *)
Lemma euclidean_top_middle_jacobian_compose (R:realType) m mu n
    (L:Hom (R_n R m) (R_n R mu)) (D:Hom (R_n R mu) (R_n R n)):
  euclidean_linear_jacobian mu (hom_comp D L)=
    euclidean_linear_jacobian mu D*euclidean_linear_jacobian mu L.
Proof.
pose hPL:=exterior_operator_normP (euclidean_two_nonzero R)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R mu)
  (@coordinate_basisP R m) (hom_as_linear L) mu.
pose hPC:=exterior_operator_normP (euclidean_two_nonzero R)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (@coordinate_basisP R m) (hom_as_linear (hom_comp D L)) mu.
have hBound:euclidean_linear_jacobian mu (hom_comp D L)<=
    euclidean_linear_jacobian mu D*euclidean_linear_jacobian mu L.
  apply:(operator_norm_le_unit hPC _).2=>x hx.
  have hScale:=euclidean_top_middle_exterior_scale L D x.
  rewrite /exterior_norm in hScale; rewrite hScale.
  exact:(ler_wpM2l (euclidean_linear_jacobian_nonnegative mu D)
    (operator_norm_unit_bound hPL hx)).
have [x [hx hValue]]:=operator_norm_attained hPL.
have hReverse:=operator_norm_unit_bound hPC hx.
have hScale:=euclidean_top_middle_exterior_scale L D x.
rewrite /exterior_norm in hScale; rewrite hScale hValue in hReverse.
apply/eqP; by rewrite eq_le hBound hReverse.
Qed.
