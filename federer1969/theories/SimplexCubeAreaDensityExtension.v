(** Federer (1969), 4.1.27, p. 384:
    the exact original full-fibre density of
    4.1.25 agrees with the printed simplex
    field on its original domain. Injectivity
    is required only on C, and
    zero off-cube coefficients remain in each fibre. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers
  CurrentMapDifferential CurrentSimplexFrame EuclideanOpenUnitCube
  CharacteristicFunctionUP CharacteristicFunctionSealed PartialFunctionUP PartialFunctionExtensionUP
  CurrentAreaNormalisedImageSealed CurrentAreaFibreSumUP CurrentAreaFibreDensityUP
  CurrentAreaFibreDensitySealed CurrentAreaFibreOutsideSupport
  CurrentAreaFibreSingleSupport SimplexCubeParametrisationUP
  SimplexCubeParametrisationSealed SimplexCubeExactImage SimplexCubeInjectivity
  SimplexCubeAreaSummand SimplexHausdorffDensityUP SimplexHausdorffDensitySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simplex_cube_area_density_extension]: the precise
    application of the preceding full-fibre formula
    giving eta=zeta/|zeta| on f(C)
    and eta=0 elsewhere, in 4.1.27,
    p. 384. The class-one representative
    has only the proved original cube
    map and differential values as hypotheses
    at this supporting stage. *)
Theorem simplex_cube_area_density_extension (R:realType) (h2:(1+1:R)!=0) n m
    (v:'I_(m.+1)->R_n R n) (G:R_n R m->R_n R n)
    (raw:R_n R m->exterior_power (R_n R m) m):
  is_nondegenerate_current_simplex v->
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) (fun _=>True) G->
  (forall x,euclidean_open_unit_cube x->G x=@SimplexCubeParametrisation.value R n m v x)->
  (forall x,euclidean_open_unit_cube x->
    @current_map_differential R m n (fun _=>True) G x=
      @current_map_differential R m n (fun _=>True)
        (@SimplexCubeParametrisation.value R n m v) x)->
  (forall x,raw x=(@CharacteristicFunction.value R (R_n R m)
      (@euclidean_open_unit_cube R m) x)*:
      e_lambda (@coordinate_basis R m) (ord_tuple m))->
  is_partial_function_total_extension
    (@CurrentAreaFibreDensity.value R h2 (R_n R m) n m G
      (@CurrentAreaNormalisedImage.value R m n G raw))
    (@SimplexHausdorffDensity.value R n m v).
Proof.
move=>hIndependent hClass hAgreement hDifferential hRaw.
pose C:=@euclidean_open_unit_cube R m.
pose F:=@SimplexCubeParametrisation.value R n m v.
pose u:=@CurrentAreaNormalisedImage.value R m n G raw.
pose w:=@SimplexHausdorffDensity.value R n m v.
pose hW:=@SimplexHausdorffDensity.laws R n m v.
have hImages:G @` C=simplex_positive_barycentric_image v.
  rewrite -(@simplex_cube_image R n m v).
  apply/seteqP;split.
  - move=>y [x hX <-];exists x;first exact:hX.
    exact:esym (hAgreement x hX).
  - move=>y [x hX <-];exists x;first exact:hX.
    exact:hAgreement x hX.
have hInside:forall x,C x->partial_function_graph u x (simplex_normalised_orientation v).
  exact:(@simplex_cube_area_summand_inside R h2 n m v G raw hRaw
    hIndependent hClass hDifferential).
have hOutside:forall x z,~C x->partial_function_graph u x z->z=0.
  exact:(@simplex_cube_area_summand_outside R n m G raw hRaw).
move=>y eta hEta.
have hSum:=(@CurrentAreaFibreDensity.laws R h2 (R_n R m) n m G u y eta).1 hEta.
case:(pselect (simplex_positive_barycentric_image v y))=>hY.
- rewrite (simplex_hausdorff_density_inside hW hY).
  have[x hX hValue]: (G @` C) y by rewrite hImages.
  symmetry;apply:(@current_area_fibre_sum_single_support R h2 (R_n R m) n m G u
    y eta x (simplex_normalised_orientation v) hSum hValue (hInside x hX)).
  move=>z a hG hDifferent hGraph.
  case:(pselect (C z))=>hZ;last exact:(hOutside z a hZ hGraph).
  have hF:F z=F x by rewrite /F -(hAgreement z hZ) -(hAgreement x hX) hG hValue.
  have hEqual:z=x:=@simplex_cube_parametrisation_injective R n m v hIndependent
    z x hZ hX hF.
  by rewrite hEqual eqxx in hDifferent.
- rewrite (simplex_hausdorff_density_outside hW hY).
  symmetry;apply:(@current_area_fibre_outside_support R h2 m n G raw C y eta).
  + move=>x hX;by rewrite hRaw
      (characteristic_off_set (@CharacteristicFunction.laws R (R_n R m) C) hX) scale0r.
  + by rewrite hImages.
  + exact:hSum.
Qed.
