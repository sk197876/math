(** Federer (1969), 4.1.7, p. 356: the
    original constant forms (DX)_lambda and constant
    multivectors e_lambda are actual smooth fields.
    Their carriers and representatives remain opaque. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms
  CurrentSpaces CurrentVectorSpaces SmoothConstantUP SmoothConstantSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentConstantFields.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.

(** Source for [current_constant_form]: the original
    constant smooth covector field, supporting
    Federer 4.1.7, p. 356. *)
Definition current_constant_form m:Hom (A_m X R^o m) (@current_smooth_space R h2 n U hU m):=
  @SmoothConstant.operator R X (A_m X R^o m) NX (@current_form_comass R h2 n m)
    hNX (@current_form_comass_real_norm R h2 n m) U hU
    (@current_smooth_space R h2 n U hU m) (@current_smooth_value R h2 n U hU m)
    (@current_smooth_space_laws R h2 n U hU m).

(** Source for [current_constant_form_values]: exact
    original covector values, supporting Federer
    4.1.7, p. 356. *)
Lemma current_constant_form_values m phi x:U x->
  @current_smooth_value R h2 n U hU m (current_constant_form m phi) x=phi.
Proof. exact:SmoothConstant.laws. Qed.

(** Source for [current_constant_vector]: the original
    constant smooth multivector field, supporting
    Federer 4.1.7, p. 356. *)
Definition current_constant_vector m:Hom (exterior_power X m) (@current_vector_smooth_space R h2 n U hU m):=
  @SmoothConstant.operator R X (exterior_power X m) NX (@current_vector_mass R h2 n m)
    hNX (@current_vector_mass_real_norm R h2 n m) U hU
    (@current_vector_smooth_space R h2 n U hU m) (@current_vector_smooth_value R h2 n U hU m)
    (@current_vector_smooth_space_laws R h2 n U hU m).

(** Source for [current_constant_vector_values]: exact
    original multivector values, supporting Federer
    4.1.7, p. 356. *)
Lemma current_constant_vector_values m xi x:U x->
  @current_vector_smooth_value R h2 n U hU m (current_constant_vector m xi) x=xi.
Proof. exact:SmoothConstant.laws. Qed.
End CurrentConstantFields.
