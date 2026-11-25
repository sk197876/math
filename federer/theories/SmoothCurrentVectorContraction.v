(** Federer (1969), 4.1.7, p. 356: the
    original smooth multivector field contracted by
    a smooth form is an actual smooth
    multivector field. Use the opaque bilinear
    multiplier and the characteristic interior laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms ExteriorGrading
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentVectorSpaces
  CurrentVectorContraction SmoothBilinearMultiplierSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothCurrentVectorContraction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (fun m=>A_m X R^o m).
Local Notation Z := (fun m=>exterior_power X m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (fun m=>@current_form_comass R h2 n m).
Local Notation hNY := (fun m=>@current_form_comass_real_norm R h2 n m).
Local Notation NZ := (fun m=>@current_vector_mass R h2 n m).
Local Notation hNZ := (fun m=>@current_vector_mass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (fun m=>@current_smooth_space R h2 n U hU m).
Local Notation ev := (fun m=>@current_smooth_value R h2 n U hU m).
Local Notation hE := (fun m=>@current_smooth_space_laws R h2 n U hU m).
Local Notation V := (fun m=>@current_vector_smooth_space R h2 n U hU m).
Local Notation vv := (fun m=>@current_vector_smooth_value R h2 n U hU m).
Local Notation hV := (fun m=>@current_vector_smooth_space_laws R h2 n U hU m).
Local Notation Fin := (fun m=>@current_form_finite_basis R h2 n m).
Local Notation VFin := (fun m=>@current_vector_finite_basis R h2 n m).
Local Notation B := (@current_vector_contraction R h2 X k p).
Local Notation hB := (@current_vector_contraction_bilinear R h2 X k p).

(** Source for [smooth_current_vector_contraction]:
    the original actual smooth field xi
    contracted phi, supporting the seventh and
    eighth displayed identities of Federer
    4.1.7, p. 356. *)
Definition smooth_current_vector_contraction (xi:V (k+p)):Hom (E k) (V p):=
  @SmoothBilinearMultiplier.operator R X (Z (k+p)) (Y k) (Z p) NX (NZ (k+p)) (NY k) (NZ p)
    hNX (hNZ (k+p)) (hNY k) (hNZ p) U (V (k+p)) (E k) (V p)
    (vv (k+p)) (ev k) (vv p) (hV (k+p)) (hE k) (hV p) (VFin (k+p)) (Fin k) B hB xi.

(** Source for [smooth_current_vector_contraction_values]:
    exact original pointwise left interior,
    supporting Federer 4.1.7, p. 356. *)
Lemma smooth_current_vector_contraction_values xi phi x:U x->
  vv p (smooth_current_vector_contraction xi phi) x=B (vv (k+p) xi x) (ev k phi x).
Proof. exact:SmoothBilinearMultiplier.laws. Qed.
End SmoothCurrentVectorContraction.
