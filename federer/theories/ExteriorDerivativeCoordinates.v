(** Federer (1969), 4.1.6, pp. 352–353: public
    coordinate and partial-domain laws of the original
    exterior derivative. The operator has exactly the
    differentiability domain; addition and scalar
    multiplication are proved using actual differentials. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialArithmetic
  GrassmannAbbreviations FiniteCoordinates AlternatingForms ScalarTensorContraction
  EuclideanCoordinateForms MixedAlternatingProduct ExteriorDifferentialUP
  ExteriorDifferentialExistence ExteriorDifferentialSealed ExteriorDifferentialLinearLaws
  PartialFunctionUP ExteriorDerivativeUP ExteriorDerivativeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_differential_coordinate_formula]:
    d phi=sum_j DX_j wedge D_j phi,
    Federer 4.1.6, p. 353. This is
    deduced from the signed definition, in every degree. *)
Theorem exterior_differential_coordinate_formula (R:realType) (h2:(1+1:R)!=0)
    n (W:lmodType R) m (L:Hom (R_n R n) (A_m (R_n R n) W m)):
  @ExteriorDifferential.value R h2 n W m L=
    \sum_(j:'I_n) mixed_form_product h2 (@scalar_action_bilinear R W)
      (euclidean_coordinate_form j) (L (@coordinate_basis R n j)).
Proof.
exact:(exterior_differential_value_unique (@ExteriorDifferential.laws R h2 n W m L)
  (@euclidean_exterior_differential_witness_laws R h2 n W m L)).
Qed.

(** Source for [exterior_derivative_exact_domain]: the
    original d phi exists at exactly the points where
    D phi exists, Federer 4.1.6,
    p. 352, including empty and zero-dimensional domains. *)
Theorem exterior_derivative_exact_domain (R:realType) (h2:(1+1:R)!=0)
    n (W:lmodType R) (NV:R_n R n->R) (hNV:is_real_norm NV)
    m (NP:A_m (R_n R n) W m->R) (hNP:is_real_norm NP)
    (U:R_n R n->Prop) (phi:R_n R n->A_m (R_n R n) W m) a:
  partial_function_domain (@ExteriorDerivative.value R (R_n R n) W NV hNV m NP hNP U phi) a <->
    exists L,has_norm_differential NV NP U phi a L.
Proof.
split.
- move=>[b hB]; have [L [hL _]]:has_exterior_derivative NV NP U phi a b.
    exact:(@ExteriorDerivative.laws R (R_n R n) W NV hNV m NP hNP U phi a b).1 hB.
  by exists L.
- move=>[L hL]; exists (@ExteriorDifferential.value R h2 n W m L).
  apply:(@ExteriorDerivative.laws R (R_n R n) W NV hNV m NP hNP U phi a _).2.
  exists L; split=>//; exact:ExteriorDifferential.laws.
Qed.

(** Source for [exterior_derivative_add]: the second
    displayed identity on p. 353, Federer
    4.1.6: d(phi+psi)=d phi+d psi. *)
Theorem exterior_derivative_add (R:realType) (V W:lmodType R)
    (NV:V->R) m (NP:A_m V W m->R) (hNP:is_real_norm NP)
    (U:V->Prop) (phi psi:V->A_m V W m) a (b c:A_m V W m.+1):
  has_exterior_derivative NV NP U phi a b ->has_exterior_derivative NV NP U psi a c ->
  has_exterior_derivative NV NP U (fun x=>phi x+psi x) a (b+c).
Proof.
move=>[L [hL hB]] [M [hM hC]].
exists (L+M); split.
- exact:(@norm_differential_add R V (A_m V W m) NV NP hNP U phi psi a L M hL hM).
- have hA:=exterior_differential_linear_values (1:R) hB hC.
  by rewrite !scale1r in hA.
Qed.
