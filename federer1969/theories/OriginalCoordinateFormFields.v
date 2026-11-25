(** Federer (1969), 4.1.6, pp. 351–352: the
    original DX_j and DX_lambda are constant fields,
    as are the standard e_lambda multivector fields.
    Their domain may be any original open subset,
    represented by its own carrier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Alternating ExteriorIndices CovectorProducts
  GrassmannAbbreviations FiniteCoordinates EuclideanCoordinateForms
  PointwiseFieldSpaceSealed DifferentialFormFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [original_coordinate_differential_field]:
    DX_j is the constant field with value X_j,
    Federer 4.1.6, p. 351. *)
Definition original_coordinate_differential_field (R:realType) (X:choiceType) n (j:'I_n):
    differential_form_space R X (R_n R n) R^o 1:=
  @PointwiseFieldSpace.of_function R X (A_m (R_n R n) R^o 1)
    (fun _=>euclidean_coordinate_form j).

(** Source for [original_coordinate_differential_field_values]:
    DX_j(x)=X_j at each original domain point,
    Federer 4.1.6, p. 351. *)
Lemma original_coordinate_differential_field_values (R:realType) (X:choiceType) n (j:'I_n) x:
  @differential_form_value R X (R_n R n) R^o 1
    (@original_coordinate_differential_field R X n j) x=euclidean_coordinate_form j.
Proof. exact:PointwiseFieldSpace.value_of_function. Qed.

(** Source for [original_coordinate_product_field]: the
    original field DX_lambda has the increasing
    coordinate product as constant value,
    Federer 4.1.6, pp. 351–352. *)
Definition original_coordinate_product_field (R:realType) (h2:(1+1:R)!=0)
    (X:choiceType) n m (lambda:Lambda n m):differential_form_space R X (R_n R n) R^o m:=
  @PointwiseFieldSpace.of_function R X (A_m (R_n R n) R^o m)
    (fun _=>@omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) m lambda).

(** Source for [original_coordinate_product_field_values]:
    DX_lambda(x)=X_lambda, the first displayed
    equation on p. 352, Federer 4.1.6. *)
Lemma original_coordinate_product_field_values (R:realType) (h2:(1+1:R)!=0)
    (X:choiceType) n m (lambda:Lambda n m) x:
  @differential_form_value R X (R_n R n) R^o m
    (@original_coordinate_product_field R h2 X n m lambda) x=
      @omega_lambda R h2 (R_n R n) n (@euclidean_coordinate_form R n) m lambda.
Proof. exact:PointwiseFieldSpace.value_of_function. Qed.

(** Source for [original_coordinate_multivector_field]: the
    standard e_lambda is a constant multivector field,
    Federer 4.1.6, p. 352. *)
Definition original_coordinate_multivector_field (R:realType) (X:choiceType)
    n m (lambda:Lambda n m):multivector_field_space R X (R_n R n) m:=
  @PointwiseFieldSpace.of_function R X (exterior_power (R_n R n) m)
    (fun _=>e_lambda (@coordinate_basis R n) (val lambda)).

(** Source for [original_coordinate_multivector_field_values]:
    e_lambda(x)=e_lambda at each original point,
    Federer 4.1.6, p. 352. *)
Lemma original_coordinate_multivector_field_values (R:realType) (X:choiceType)
    n m (lambda:Lambda n m) x:
  @multivector_field_value R X (R_n R n) m
    (@original_coordinate_multivector_field R X n m lambda) x=
      e_lambda (@coordinate_basis R n) (val lambda).
Proof. exact:PointwiseFieldSpace.value_of_function. Qed.
