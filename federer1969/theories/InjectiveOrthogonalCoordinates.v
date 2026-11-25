(** Federer (1969), 3.2.22, p. 259: supporting
    orthonormal coordinates on the image of an injective
    differential. Polar factorisation supplies existence; no
    new coordinate selection is made globally. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  LinearBasis FiniteBasisComparison FiniteIndependence IndependentMap OrthogonalMaps PolarFactorisationUP
  PolarInjection EuclideanLinearMaps LinearRetraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [injective_orthogonal_coordinates_exists]:
    supporting coordinate comparison in Federer 3.2.22,
    p. 259, from polar factorisation in 1.7.3,
    p. 30. An injective D factors through an orthogonal
    injection O and an invertible source endomorphism K.
    Both inverse laws are proved; no inverse hypothesis is added. *)
Lemma injective_orthogonal_coordinates_exists (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)):
  injective D ->exists (O:Hom (R_n R m) (R_n R n))
    (K Ki:Hom (R_n R m) (R_n R m)),
    is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) (hom_as_linear O) /\
    (forall x,O (K x)=D x) /\ cancel K Ki /\ cancel Ki K.
Proof.
move=>hD.
have hImages:finite_independent (fun i=>D (@coordinate_basis R m i)):=
  finite_independent_map hD (finite_basis_independent (@coordinate_basisP R m)).
have [K [O hFact]]:=@polar_injection_factorisation_exists R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  (fun i=>D (@coordinate_basis R m i)) hImages (hom_as_linear D).
have hK:injective K.
  move=>x y hEq; apply:hD; rewrite -(injection_factor_equation hFact x)
    -(injection_factor_equation hFact y) hEq; reflexivity.
pose Ki:=linear_retraction hK.
have hLeft:cancel K Ki:=linear_retractionK hK.
have hRight:cancel Ki K.
  move=>x; have [y hy]:=euclidean_injective_surjective hK x.
  by rewrite -hy hLeft.
exists (hom_of_linear O),(hom_of_linear K),(hom_of_linear Ki).
split; first exact:(injection_factor_orthogonal hFact).
split; first exact:(injection_factor_equation hFact).
by split.
Qed.
