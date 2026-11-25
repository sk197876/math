(** Federer (1969), 4.1.7, pp. 357–358:
    actual zero-dimensional fundamental-current regressions.
    The established empty-product convention makes
    E^0 a unit point current with
    mass one and an everywhere orientation.
    No positive-degree boundary is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct FiniteExteriorPowers CurrentDomain CurrentSpaces
  CurrentMassSealed CurrentMassRepresentation NormalisedCurrentSealed CurrentOrientationSealed
  EuclideanFundamentalCurrent EuclideanFundamentalCurrentVariation EuclideanFundamentalCurrentOrientation
  EuclideanFullDomainMeasure EuclideanLebesgueDimensions OpenSubspaceMeasure PointMassMeasure PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanCurrentEndpointExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0).
Local Notation N := (inner_norm (@euclidean_inner_productP R 0)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X N x).
Local Notation FT := (current_domain R 0 (fun _=>True)).
Local Notation E := (@euclidean_fundamental_current R h2 0).
Let hE:=@euclidean_fundamental_current_representable R h2 0.

(** Source for [zero_dimensional_fundamental_current_unit_mass]:
    the actual E^0 has mass one,
    a boundary regression for Federer 4.1.7,
    p. 358. Its literal full-domain
    variation reduces to the earlier unit
    point mass, including the empty exterior product. *)
Example zero_dimensional_fundamental_current_unit_mass:
  @CurrentMass.value R h2 0 0%N (fun _=>True) hFull E = 1%E.
Proof.
rewrite (@current_represented_mass_total R h2 0 0%N (fun _=>True) hFull E hE)
  (@euclidean_fundamental_current_variation R h2 0 hE).
change (@point_mass R X 0 (set_val @` (setT:set FT)) = 1%E).
apply:point_mass_in.
exists (@euclidean_full_domain_point R 0 0);by [].
Qed.

(** Source for [zero_dimensional_fundamental_current_orientation]:
    the actual original orientation of E^0
    is the empty coordinate product at
    every point, a regression for Federer
    4.1.7, p. 358. This uses
    the full original partial graph and
    the proved representation, not a conull restriction. *)
Example zero_dimensional_fundamental_current_orientation (x:FT):
  partial_function_graph
    (@CurrentOrientation.value R h2 0 0%N (fun _=>True) hFull E hE) x
    (e_lambda (@coordinate_basis R 0) (ord_tuple 0)).
Proof. exact:(@euclidean_fundamental_current_orientation_everywhere R h2 0 hE x). Qed.
End EuclideanCurrentEndpointExamples.
