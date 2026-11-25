(** Federer (1969), 4.1.27, p. 384:
    the preceding normalized differential summand is
    the fixed simplex orientation on the
    original cube and zero at every
    defined off-cube point. A compact class-one
    representative is permitted only when its
    actual map and differential agree on C. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct ExteriorGrading ExteriorMaps
  FiniteExteriorPowers EuclideanLinearJacobian CurrentMapDifferential
  CurrentClassOneCompactPlateau EuclideanOpenUnitCube CurrentSimplexFrame
  CharacteristicFunctionUP CharacteristicFunctionSealed PartialFunctionUP
  CurrentAreaNormalisedImageUP CurrentAreaNormalisedImageSealed
  SimplexCubeParametrisationUP SimplexCubeParametrisationSealed
  SimplexCubeNormalisedDifferential SimplexHausdorffDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SimplexCubeAreaSummand.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable v:'I_(m.+1)->R_n R n.
Variable G:R_n R m->R_n R n.
Variable raw:R_n R m->exterior_power (R_n R m) m.
Local Notation C:=(@euclidean_open_unit_cube R m).
Local Notation F:=(@SimplexCubeParametrisation.value R n m v).
Local Notation Full:=(fun _:R_n R m=>True).
Local Notation DG:=(fun x=>@current_map_differential R m n Full G x).
Local Notation DF:=(fun x=>@current_map_differential R m n Full F x).
Local Notation u:=(@CurrentAreaNormalisedImage.value R m n G raw).
Hypothesis hRaw:forall x,raw x=(@CharacteristicFunction.value R (R_n R m) C x)*:
  e_lambda (@coordinate_basis R m) (ord_tuple m).

(** Source for [simplex_cube_area_summand_outside]: every defined
    original coefficient off C is zero,
    in the application of 4.1.25
    to the cube in 4.1.27,
    p. 384. The original partial differential
    domain is not extended by this assertion. *)
Theorem simplex_cube_area_summand_outside x w:
  ~C x->partial_function_graph u x w->w=0.
Proof.
move=>hOutside hGraph.
have[D [_ [_ hFormula]]]:=(@CurrentAreaNormalisedImage.laws R m n G raw x w).1 hGraph.
rewrite -hFormula /current_area_normalised_image_coefficient hRaw
  (characteristic_off_set (@CharacteristicFunction.laws R (R_n R m) C) hOutside)
  scale0r linear0 scaler0.
by [].
Qed.

(** Source for [simplex_cube_area_summand_inside]: the original
    nondegenerate cube contributes exactly zeta/|zeta|
    at each of its points, in
    4.1.27, p. 384. Every needed
    differential and its positive Jacobian follow
    from class one and exact original
    differential agreement on C. *)
Theorem simplex_cube_area_summand_inside:
  is_nondegenerate_current_simplex v->
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) Full G->
  (forall x,C x->DG x=DF x)->
  forall x,C x->partial_function_graph u x (simplex_normalised_orientation v).
Proof.
move=>hIndependent hClass hDifferential x hX.
apply:(@CurrentAreaNormalisedImage.laws R m n G raw x
  (simplex_normalised_orientation v)).2.
exists (DG x);split.
- exact:(@current_class_one_map_differential_actual R m n Full G hClass x Logic.I).
- split.
  + rewrite (hDifferential x hX).
    exact:lt0r_neq0 (@simplex_cube_jacobian_positive R h2 n m v x hIndependent hX).
  + rewrite /current_area_normalised_image_coefficient hRaw
      (characteristic_on_set (@CharacteristicFunction.laws R (R_n R m) C) hX)
      scale1r (hDifferential x hX).
    exact:(@simplex_cube_normalised_top_differential R n m v x hX).
Qed.
End SimplexCubeAreaSummand.
