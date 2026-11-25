(** Federer (1969), 4.1.7, p. 357: the actual
    covector and multivector norms used for currents.
    Positive degrees use the sealed mass and comass;
    degree zero uses the established absolute-scalar
    norm correction from 1.8.1, p. 38. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP InnerProductUP InnerNorm
  InnerExterior InnerExteriorPositivity ExteriorGrading AlternatingForms
  ExteriorNorm ExteriorCovectorInner GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct Comass Mass HilbertFormCompactness
  ComassRealNorm MassRealNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCoefficientNorms.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation V := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation e := (@coordinate_basis R n).
Local Notation he := (@coordinate_basisP R n).

(** Source for [current_form_comass]: the original
    norm on Y=A^m(R^n) in Federer 4.1.7, p. 357,
    retaining the earlier degree-zero convention. *)
Definition current_form_comass m:A_m V R^o m->R:=
  match m as d return A_m V R^o d->R with
  |0%N=>@exterior_covector_norm R h2 V B hB n e he 0
  |k.+1=>@comass R h2 V B hB n e he k.+1 (ltn0Sn k)
  end.

(** Source for [current_vector_mass]: the original
    dual norm on Lambda_m(R^n) in Federer 4.1.7,
    p. 357, with absolute scalar norm in degree zero. *)
Definition current_vector_mass m:exterior_power V m->R:=
  match m as d return exterior_power V d->R with
  |0%N=>@exterior_norm R h2 V B hB 0
  |k.+1=>@mass R h2 V B hB n e he k.+1 (ltn0Sn k)
  end.

(** Source for [current_form_comass_real_norm]: the
    norm premise of 4.1.5 is satisfied by the actual
    covectors in Federer 4.1.7, p. 357, at every degree. *)
Lemma current_form_comass_real_norm m:is_real_norm (@current_form_comass m).
Proof.
case:m=>[|k].
- exact:(@inner_norm_real_norm R (A_m V R^o 0)
    (@exterior_covector_inner R h2 V B hB n e he 0)
    (@exterior_covector_inner_productP R h2 V B hB n e he 0)).
- exact:(@comass_real_norm R h2 V B hB k.+1 (ltn0Sn k) _
    (@comassP R h2 V B hB n e he k.+1 (ltn0Sn k))).
Qed.

(** Source for [current_vector_mass_real_norm]: the
    actual mass is a norm on the vector dual in
    Federer 4.1.7, p. 357, including degree zero. *)
Lemma current_vector_mass_real_norm m:is_real_norm (@current_vector_mass m).
Proof.
case:m=>[|k].
- exact:(@inner_norm_real_norm R (exterior_power V 0)
    (@exterior_inner_form R h2 V B hB 0)
    (@exterior_inner_productP R h2 V B hB 0)).
- exact:(@mass_real_norm R h2 V B hB n e he k.+1 (ltn0Sn k) _
    (@comassP R h2 V B hB n e he k.+1 (ltn0Sn k)) _
    (@massP R h2 V B hB n e he k.+1 (ltn0Sn k))).
Qed.
End CurrentCoefficientNorms.
