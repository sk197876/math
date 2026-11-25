(** Federer (1969), 4.1.26, p. 383: the
    normalized top exterior image of the standard
    orientation is the determinant sign times that
    orientation. This is the specialization of
    4.1.25 used in the printed proof on p. 384.
    Every dimension, including zero, is retained. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading FiniteExteriorPowers ExteriorMaps ExteriorDeterminant EuclideanLinearMaps
  EuclideanLinearJacobian CurrentAreaNormalisedImageUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [top_degree_normalised_determinant]: the
    summand of degree f restricted to A is
    sign det Df(x), Federer 4.1.26, p. 383,
    by 1.3.4 and the square Jacobian formula.
    This algebraic law is used only at an
    actual differential in the later partial graph. *)
Theorem top_degree_normalised_determinant (R:realType) m
    (D:Hom (R_n R m) (R_n R m)) (a:R) (x:R_n R m):
  @current_area_normalised_image_coefficient R m m
    (fun _=>a*:e_lambda (@coordinate_basis R m) (ord_tuple m)) x D=
    (a*Num.sg (@euclidean_det R m (hom_as_linear D)))*:
      e_lambda (@coordinate_basis R m) (ord_tuple m).
Proof.
pose d:=@euclidean_det R m (hom_as_linear D).
have hRatio:`|d|^-1*d=Num.sg d.
  case:(ltgtP d 0)=>[hNegative|hPositive|hZero].
  - have hNonzero:d!=0 by apply/eqP=>h;by rewrite h ltxx in hNegative.
    by rewrite (ltr0_norm hNegative) (ltr0_sg hNegative) invrN mulNr mulVf.
  - have hNonzero:d!=0 by apply/eqP=>h;by rewrite h ltxx in hPositive.
    by rewrite (gtr0_norm hPositive) (gtr0_sg hPositive) mulVf.
  - by rewrite hZero normr0 invr0 mulr0 sgr0.
have hTop:exterior_power_map (hom_as_linear D) m
    (e_lambda (@coordinate_basis R m) (ord_tuple m))=
    d*:e_lambda (@coordinate_basis R m) (ord_tuple m).
  exact:(@detE R (euclidean_two_nonzero R) m (R_n R m)
    (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear D) _).
rewrite /current_area_normalised_image_coefficient linearZ hTop
  !scalerA euclidean_linear_jacobian_determinant.
by rewrite -mulrA mulrCA hRatio.
Qed.
