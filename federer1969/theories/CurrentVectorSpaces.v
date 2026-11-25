(** Federer (1969), 4.1.7, pp. 355–357: actual
    smooth multivector fields, with the original
    finite-dimensional mass norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorIndices FiniteExteriorPowers
  LinearBasis FiniteCoordinates FiniteOrdinalBasis CurrentCoefficientNorms Distributions SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentVectorSpaces.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (fun m=>exterior_power X m).
Local Notation NY := (fun m=>@current_vector_mass R h2 n m).
Local Notation hNY := (fun m=>@current_vector_mass_real_norm R h2 n m).

(** Source for [current_vector_finite_basis]: the
    original coordinate multivectors form a finite
    basis, supporting Federer 4.1.7, pp. 355–357,
    by 1.3.4, p. 17. *)
Lemma current_vector_finite_basis m:
  exists k,exists b:'I_k->Y m,is_basis b.
Proof.
pose I:finType:=Finite.clone (Lambda n m) _.
pose e:I->Y m:=fun lambda=>e_lambda (@coordinate_basis R n) (val lambda).
have he:is_basis e:=@finite_e_lambda_basis R n X (@coordinate_basis R n)
  (@coordinate_basisP R n) h2 m.
exists #|I|,(fun i=>e (enum_val i)); exact:finite_ordinal_basis.
Qed.
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.

(** Source for [current_vector_smooth_space]: the
    actual smooth multivector fields of Federer
    4.1.7, pp. 355–356. *)
Definition current_vector_smooth_space m:lmodType R:=
  @distribution_smooth_space R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_vector_smooth_value]: actual
    pointwise multivector values, supporting Federer
    4.1.7, pp. 355–356. *)
Definition current_vector_smooth_value m:current_vector_smooth_space m->X->Y m:=
  @distribution_smooth_value R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_vector_smooth_space_laws]: exact
    smooth field realization, supporting Federer
    4.1.7, pp. 355–356. *)
Definition current_vector_smooth_space_laws m:
    is_smooth_function_space hNX (hNY m) U (@current_vector_smooth_value m):=
  @distribution_smooth_laws R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_vector_smooth_derivatives]: actual
    higher multivector derivatives, supporting the
    current product rules of Federer 4.1.7, p. 356. *)
Definition current_vector_smooth_derivatives m:=
  @distribution_smooth_derivatives R X (Y m) NX (NY m) hNX (hNY m) U hU.

(** Source for [current_vector_smooth_derivative_laws]:
    the original derivative graphs, supporting
    Federer 4.1.7, p. 356. *)
Definition current_vector_smooth_derivative_laws m:
    @is_smooth_function_derivatives R X (Y m) NX (NY m) hNX (hNY m) U
      (current_vector_smooth_space m) (@current_vector_smooth_value m)
      (@current_vector_smooth_derivatives m):=
  @distribution_smooth_derivative_laws R X (Y m) NX (NY m) hNX (hNY m) U hU.
End CurrentVectorSpaces.
