(** Federer (1969), 4.1.7, p. 356: actual
    directional derivatives of forms and currents.
    Coordinate directions give the printed D_j. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentCoefficientNorms CurrentVectorSpaces
  OpenFamilyTopologyUP SmoothDirectionalDerivativeUP SmoothDirectionalDerivativeSealed
  SmoothDirectionalEvaluation SmoothTestTopology DistributionDirectionalDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentVectorDirectionalDerivative.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_vector_mass R h2 n m).
Local Notation hNY := (@current_vector_mass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (@current_vector_smooth_space R h2 n U hU m).
Local Notation ev := (@current_vector_smooth_value R h2 n U hU m).
Local Notation hE := (@current_vector_smooth_space_laws R h2 n U hU m).
Local Notation D := (@current_vector_smooth_derivatives R h2 n U hU m).
Local Notation hD := (@current_vector_smooth_derivative_laws R h2 n U hU m).
Variable v:X.


(** Source for [current_vector_smooth_directional_derivative]:
    actual D_v on the original smooth multivector
    fields, supporting Federer 4.1.7, p. 356. *)
Definition current_vector_smooth_directional_derivative:Hom E E:=
  @SmoothDirectionalDerivative.operator R X Y NX NY hNX hNY U E ev hE D hD v.

(** Source for [current_vector_smooth_directional_derivative_laws]:
    the actual derivative evaluates the original first
    differential, supporting Federer 4.1.7, p. 356. *)
Definition current_vector_smooth_directional_derivative_laws:
    @is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v
      current_vector_smooth_directional_derivative:=
  @SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY U E ev hE D hD v.
End CurrentVectorDirectionalDerivative.
