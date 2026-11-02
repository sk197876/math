(** Federer (1969), 3.1.22, pp. 235–236: all five
    differential criteria on a class-one Euclidean submanifold. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP NormDifferentialUP PartialFunctionUP RelativeDifferentialUP RelativeSubmanifoldCriteriaUP
  EuclideanSubmanifoldUP SubmanifoldLocalGeometry SubmanifoldCoordinateSystems
  RelativeRetractionCriterion RelativeCoordinateDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Criteria.
Variable R:realType.
Variables n mu:nat.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R mu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R mu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R mu)).
Variables (A B:set X) (f:X->Y) (a:X) (L:partial_function X Y).
Local Notation Rel:=(@has_relative_norm_differential R X Y NX NY hNX A B f a L).

(** Source for [submanifold_relative_differential_criteria]: all
    equivalences (1), (2), (3), [2] and [3] in Federer
    3.1.22, pp. 235–236. Retractions and coordinate systems
    are actual maps, with existence supplied by 3.1.19. The
    differential graphs retain the tangent space as their exact domain. *)
Theorem submanifold_relative_differential_criteria :
  @is_euclidean_submanifold R n mu 1 B -> B a -> B `<=` A ->
  (Rel <-> @relative_some_retraction_differential R X Y NX NY hNX B f a L) /\
  (Rel <-> @relative_every_retraction_differential R X Y NX NY hNX B f a L) /\
  (Rel <-> @relative_some_coordinate_differential R X Z Y NX NZ NY hNX hNZ B f a L) /\
  (Rel <-> @relative_every_coordinate_differential R X Z Y NX NZ NY hNX hNZ B f a L).
Proof.
move=>hB ha hBA.
have [T [r [hTa hr]]]:=submanifold_local_retractions hB ha.
have [Tc [V [phi [psi [E [J [hat [hc [hphi hpsi]]]]]]]]]:=
  submanifold_differentiable_coordinates_exist hB ha.
have hR U rho hU hret:=@relative_retraction_differential_criterion R X Y NX NY hNX hNY
  A B U f rho a L ha hBA hU hret.
have hC U W p s D K hsys hb hDp hDs:=
  @relative_coordinate_differential_criterion R X Z Y NX NZ NY hNX hNZ hNY
    A B U W p s f a D K L hsys ha hb hBA hDp hDs.
split.
- split.
  + move=>hrel; exists T,r; split=>//; split=>//; exact ((hR T r hTa hr).1 hrel).
  + move=>[U [rho [hU [hret hd]]]]; exact ((hR U rho hU hret).2 hd).
split.
- split.
  + move=>hrel U rho hU hret; exact ((hR U rho hU hret).1 hrel).
  + move=>hall; exact ((hR T r hTa hr).2 (hall T r hTa hr)).
split.
- split.
  + move=>hrel; exists Tc,V,phi,psi,E,J; split=>//; split=>//; split=>//; split=>//.
    exact ((hC Tc V phi psi E J hc hat hphi hpsi).1 hrel).
  + move=>[U [W [p [s [D [K [hb [hsys [hDp [hDs hd]]]]]]]]]].
    exact ((hC U W p s D K hsys hb hDp hDs).2 hd).
- split.
  + move=>hrel U W p s D K hb hsys hDp hDs.
    exact ((hC U W p s D K hsys hb hDp hDs).1 hrel).
  + move=>hall; exact ((hC Tc V phi psi E J hc hat hphi hpsi).2
      (hall Tc V phi psi E J hat hc hphi hpsi)).
Qed.
End Criteria.
