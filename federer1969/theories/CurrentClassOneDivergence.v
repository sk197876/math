(** Federer (1969), 4.1.7, p. 356: the
    divergence of a class-one multivector field
    is continuous. The original divergence map
    and its coordinate formula from 4.1.6,
    p. 354, supply the proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP NormClassOneDirectionalField
  NormClassZeroPostcompose NormClassZeroFiniteSum NormClassHigherDerivative InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanCoordinateForms ExteriorGrading
  CurrentCoefficientNorms CurrentOneCovectorMap DivergenceUP DivergenceSealed DivergenceCoordinates DivergenceDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentClassOneDivergence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (exterior_power X p.+1).
Local Notation Z := (exterior_power X p).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_vector_mass R h2 n p.+1).
Local Notation hNY := (@current_vector_mass_real_norm R h2 n p.+1).
Local Notation NZ := (@current_vector_mass R h2 n p).
Local Notation hNZ := (@current_vector_mass_real_norm R h2 n p).

(** Source for [current_class_one_divergence_field]:
    the original divergence applied to the
    actual first differential, supporting Federer
    4.1.7, p. 356. *)
Definition current_class_one_divergence_field (DXi:X->Hom X Y):X->Z:=
  fun x=>@Divergence.value R h2 n p (DXi x).

(** Source for [current_class_one_divergence_actual]:
    the candidate has the original field-divergence
    graph, supporting the class-one formulas of
    Federer 4.1.7, p. 356. *)
Theorem current_class_one_divergence_actual U xi DXi:
  is_norm_class_one_field NX NY U xi DXi ->forall x,U x->
    has_field_divergence h2 NX NY U xi x (current_class_one_divergence_field DXi x).
Proof.
move=>hXi x hx;exists (DXi x);split.
- exact:(@norm_class_one_differential R X Y NX NY U xi DXi hXi x hx).
- exact:Divergence.laws.
Qed.

(** Source for [current_class_one_divergence_continuous]:
    every class-one field has continuous actual
    divergence, supporting the Lebesgue-current
    boundary formula in Federer 4.1.7,
    p. 356. *)
Theorem current_class_one_divergence_continuous U xi DXi:
  is_norm_class_one_field NX NY U xi DXi ->
  norm_class_zero NX NZ U (current_class_one_divergence_field DXi).
Proof.
move=>hXi.
pose L j:=@current_one_covector_map R h2 n p (euclidean_coordinate_form j).
have hField j:norm_class_zero NX NZ U (fun x=>L j (DXi x (@coordinate_basis R n j))).
  apply:(@norm_class_zero_postcompose R X Y Z NX NY NZ hNY U
    (fun x=>DXi x (@coordinate_basis R n j)) (L j)).
  - exact:(@norm_class_one_directional_continuous R X Y NX NY hNX hNY U xi DXi
      (@coordinate_basis R n j) hXi).
  - exact:current_one_covector_map_bounded.
have hSum:=@norm_class_zero_finite_sum R X Z NX NZ hNX hNZ U [the finType of 'I_n]
  (fun j x=>L j (DXi x (@coordinate_basis R n j)))
  (fun x hx=>(@norm_class_one_zero R X Y NX NY U xi DXi hXi x hx).1) hField.
apply:(norm_class_zero_domain_agreement _ hSum)=>x _.
by rewrite /current_class_one_divergence_field divergence_coordinate_formula.
Qed.
End CurrentClassOneDivergence.
