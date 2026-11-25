(** Federer (1969), 4.1.23, p. 380:
    the coefficient of the scalar rectangle times
    a transverse scalar current is exactly the
    first-coordinate m-vector used in the proof.
    The scalar factor remains the original exterior
    unit, including both zero-dimensional blocks. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom FiniteCoordinates FiniteExteriorPowers GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockLinearMaps ExteriorGrading ExteriorPowers
  ExteriorMaps ExteriorHomogeneousProducts ExteriorMapNormContinuity
  CurrentCoefficientNorms CurrentCartesianVectorProduct
  CurrentCartesianCoordinateOrientation CurrentZeroDegreeExteriorLaws.
From Federer Require Import CurrentDiracDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_cartesian_zero_right_vector]:
    after identifying j+0 with j,
    the Cartesian coefficient with the
    transverse unit scalar is the original
    first-block exterior image, supporting
    Federer 4.1.23, p. 380. *)
Lemma current_cartesian_zero_right_vector (R : realType) m n j
    (u : exterior_power (R_n R m) j) :
  exterior_reindex (addn0 j)
    (@current_cartesian_vector_product R m n j 0%N u
      (@current_scalar_multivector_unit R n))=
    exterior_power_map (hom_as_linear (@euclidean_first_injection_map R m n)) j u.
Proof.
by rewrite /current_cartesian_vector_product /current_scalar_multivector_unit
  exterior_power_map_zeroth_scalar exterior_product_zeroth_scalar_right scale1r.
Qed.

(** Source for [current_cartesian_top_zero_prefix_vector]:
    the actual top-vector of R times
    the transverse zero-vector unit becomes
    e_1 wedge ... wedge e_m,
    the exact coordinate coefficient of
    Federer 4.1.23, p. 380. *)
Lemma current_cartesian_top_zero_prefix_vector (R : realType) m n :
  exterior_reindex (addn0 m)
    (@current_cartesian_vector_product R m n m 0%N
      (e_lambda (@coordinate_basis R m) (ord_tuple m))
      (@current_scalar_multivector_unit R n))=
    e_lambda (fun i : 'I_m => @coordinate_basis R (m+n) (lshift n i)) (ord_tuple m).
Proof.
rewrite current_cartesian_zero_right_vector exterior_power_map_e_lambda.
have hFamily : (hom_as_linear (@euclidean_first_injection_map R m n) \o
    @coordinate_basis R m)=
    (fun i : 'I_m => @coordinate_basis R (m+n) (lshift n i)).
  apply: funext=> i; exact: current_cartesian_first_coordinate_basis.
by rewrite hFamily.
Qed.

(** Source for [current_cartesian_top_zero_standard_vector]:
    the same coefficient uses precisely the
    standard prefix frame in the preceding
    simple-unit rotation, supporting Federer
    4.1.23, pp. 379–380.
    The ordinal equality is proved on
    its values rather than assumed. *)
Lemma current_cartesian_top_zero_standard_vector (R : realType) m n :
  exterior_reindex (addn0 m)
    (@current_cartesian_vector_product R m n m 0%N
      (e_lambda (@coordinate_basis R m) (ord_tuple m))
      (@current_scalar_multivector_unit R n))=
    e_lambda (fun i : 'I_m => @coordinate_basis R (m+n)
      (widen_ord (leq_addr n m) i)) (ord_tuple m).
Proof.
rewrite current_cartesian_top_zero_prefix_vector.
have hFamily : (fun i : 'I_m => @coordinate_basis R (m+n) (lshift n i))=
    (fun i : 'I_m => @coordinate_basis R (m+n) (widen_ord (leq_addr n m) i)).
  apply: funext=> i; congr (coordinate_basis _).
  apply: val_inj; reflexivity.
by rewrite hFamily.
Qed.
