(** Federer (1969), 4.1.6, p. 351: the
    inner products, lengths, mass and comass of fields
    are the actual pointwise Chapter 1 operations.
    At degree zero the norm convention uses absolute
    value, preserving the proved correction recorded
    in ComassZeroDegree rather than an unsigned supremum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals topology.
From Federer Require Import Hom RealNormUP NormMetric BaireFunctions
  InnerProductUP InnerExterior InnerExteriorPositivity ExteriorNorm ExteriorCovectorInner
  LinearBasis ExteriorGrading AlternatingForms Comass Mass
  PointwiseFieldSpaceSealed DifferentialFormFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_baire_differential_form]: Baire forms
    are exactly the original Baire functions with
    values in the normed form space,
    Federer 4.1.6, p. 351. *)
Definition is_baire_differential_form (R:realType) (X:topologicalType)
    (V W:lmodType R) m (N:A_m V W m->R) (hN:is_real_norm N)
    (phi:differential_form_space R X V W m):Prop:=
  @is_baire_function R X (real_norm_metric_space hN)
    (@differential_form_value R X V W m phi).

(** Source for [multivector_field_inner_product]: the
    original induced inner product at each point,
    Federer 4.1.6, p. 351, using 1.7.5. *)
Definition multivector_field_inner_product (R:realType) (h2:(1+1:R)!=0)
    (X:choiceType) (V:lmodType R) (B:V->V->R) (hB:is_inner_product B) m
    (xi eta:multivector_field_space R X V m):X->R:=
  fun x=>exterior_inner_form h2 hB
    (@multivector_field_value R X V m xi x) (@multivector_field_value R X V m eta x).

(** Source for [real_form_field_inner_product]: the
    original real covector inner product at each point,
    Federer 4.1.6, p. 351, using 1.7.5. *)
Definition real_form_field_inner_product (R:realType) (h2:(1+1:R)!=0)
    (X:choiceType) (V:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    n (e:'I_n->V) (he:is_basis e) m (phi psi:differential_form_space R X V R^o m):X->R:=
  fun x=>@exterior_covector_inner R h2 V B hB n e he m
    (@differential_form_value R X V R^o m phi x) (@differential_form_value R X V R^o m psi x).

(** Source for [multivector_field_length]: |xi|(x)
    is the Euclidean length of xi(x),
    Federer 4.1.6, p. 351. *)
Definition multivector_field_length (R:realType) (h2:(1+1:R)!=0)
    (X:choiceType) (V:lmodType R) (B:V->V->R) (hB:is_inner_product B) m
    (xi:multivector_field_space R X V m):X->R:=
  fun x=>exterior_norm h2 hB (@multivector_field_value R X V m xi x).

(** Source for [real_form_field_length]: |phi|(x)
    is the original induced Euclidean covector length,
    Federer 4.1.6, p. 351. *)
Definition real_form_field_length (R:realType) (h2:(1+1:R)!=0)
    (X:choiceType) (V:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    n (e:'I_n->V) (he:is_basis e) m (phi:differential_form_space R X V R^o m):X->R:=
  fun x=>@exterior_covector_norm R h2 V B hB n e he m
    (@differential_form_value R X V R^o m phi x).

(** Source for [multivector_field_mass]: ||xi||(x)
    is the original mass of xi(x),
    Federer 4.1.6, p. 351, with the
    absolute scalar norm in degree zero. *)
Definition multivector_field_mass (R:realType) (h2:(1+1:R)!=0)
    (X:choiceType) (V:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    n (e:'I_n->V) (he:is_basis e) m:
    multivector_field_space R X V m->X->R:=
  match m as d return multivector_field_space R X V d->X->R with
  |0%N=>fun xi x=>exterior_norm h2 hB (@multivector_field_value R X V 0 xi x)
  |k.+1=>fun xi x=>@mass R h2 V B hB n e he k.+1 (ltn0Sn k)
      (@multivector_field_value R X V k.+1 xi x)
  end.

(** Source for [real_form_field_comass]: ||phi||(x)
    is the original comass of phi(x),
    Federer 4.1.6, p. 351. The existing
    degree-zero correction uses absolute scalar value. *)
Definition real_form_field_comass (R:realType) (h2:(1+1:R)!=0)
    (X:choiceType) (V:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    n (e:'I_n->V) (he:is_basis e) m:
    differential_form_space R X V R^o m->X->R:=
  match m as d return differential_form_space R X V R^o d->X->R with
  |0%N=>fun phi x=>@exterior_covector_norm R h2 V B hB n e he 0
      (@differential_form_value R X V R^o 0 phi x)
  |k.+1=>fun phi x=>@comass R h2 V B hB n e he k.+1 (ltn0Sn k)
      (@differential_form_value R X V R^o k.+1 phi x)
  end.
