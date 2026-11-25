(** Federer (1969), 4.1.7, p. 357: E^n is
    Lebesgue measure with the original coordinate
    orientation e_1 wedge ... wedge e_n.
    Dimension zero is retained; boundary is used
    only in positive dimension. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading
  FiniteExteriorPowers CurrentSpaces CurrentDensityUP CurrentDensityAction CurrentConstantDensity
  CurrentDirectionalDerivative CurrentBoundary CurrentBoundaryDerivativeZero EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_fundamental_current]: the
    original current E^n in Federer 4.1.7,
    p. 357, defined by its already sealed
    Lebesgue-density current and coordinate orientation. *)
Definition euclidean_fundamental_current (R:realType) (h2:(1+1:R)!=0) n:
    @full_current_space R h2 n n:=
  @current_constant_density R h2 n n (e_lambda (@coordinate_basis R n) (ord_tuple n)).

(** Source for [euclidean_fundamental_current_action]:
    E^n acts by the original integral of
    the coordinate-oriented top pairing, Federer
    4.1.7, p. 357. *)
Theorem euclidean_fundamental_current_action (R:realType) (h2:(1+1:R)!=0) n:
  is_current_density_action (@euclidean_lebesgue_measure R n)
    (fun _=>e_lambda (@coordinate_basis R n) (ord_tuple n))
    (@euclidean_fundamental_current R h2 n).
Proof. exact:current_constant_density_action. Qed.

(** Source for [euclidean_fundamental_current_directional_zero]:
    D_j E^n=0 in Federer 4.1.7,
    p. 357; the same equality holds in
    every direction and at dimension zero. *)
Theorem euclidean_fundamental_current_directional_zero (R:realType) (h2:(1+1:R)!=0) n v:
  @current_directional_derivative R h2 n n (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) x) v
    (@euclidean_fundamental_current R h2 n)=0.
Proof. exact:current_constant_density_directional_zero. Qed.

(** Source for [euclidean_fundamental_current_boundary_zero]:
    boundary E^n=0 for n>0, Federer
    4.1.7, p. 357, by the original
    coordinate boundary identity. *)
Theorem euclidean_fundamental_current_boundary_zero (R:realType) (h2:(1+1:R)!=0) n:
  @current_boundary R h2 n.+1 n (fun _=>True)
    (fun x (_:True)=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R n.+1)) x)
    (@euclidean_fundamental_current R h2 n.+1)=0.
Proof.
apply:current_coordinate_derivatives_zero_boundary=>j.
exact:euclidean_fundamental_current_directional_zero.
Qed.
