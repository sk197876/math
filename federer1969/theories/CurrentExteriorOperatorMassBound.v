(** Federer (1969), 4.1.9, p. 364: the original
    homotopy mass integrand is bounded by the velocity
    norm times the j-th power of the spatial operator
    norm. Reuse the exact first-degree norm, exterior
    map estimate and mass product bound of 1.8.1, p. 39. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct ExteriorGrading ExteriorMaps ExteriorPowers
  CurrentCoefficientNorms CurrentPositiveCoefficientNorms CurrentZeroDegreeExteriorLaws
  MassEquality SimpleVectors ExteriorDegreeOneNorm CurrentExteriorProductMass
  OperatorNormUP OperatorNormSealed MassComassMaps Comass Mass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentExteriorOperatorMassBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation BX := (@euclidean_inner_product R m).
Local Notation BY := (@euclidean_inner_product R n).
Local Notation hBX := (@euclidean_inner_productP R m).
Local Notation hBY := (@euclidean_inner_productP R n).
Variable f:{linear X->Y}.

Variable L:R.
Hypothesis hL:is_operator_norm hBX hBY f L.

(** Source for [current_exterior_operator_mass_bound]: the
    actual mass of Lambda_j F eta is at most ||F||^j
    times the original mass of eta in every degree,
    supporting Federer 4.1.9, p. 364, by 1.8.1,
    p. 39. Zero-dimensional spaces and degree zero remain. *)
Theorem current_exterior_operator_mass_bound q (x:exterior_power X q):
  @current_vector_mass R h2 n q (exterior_power_map f q x)<=
    L^+q*@current_vector_mass R h2 m q x.
Proof.
case:q x=>[|k] x.
- rewrite -{1}(exterior_zeroth_inverseK x) exterior_power_map_zeroth_scalar
    current_vector_mass_zeroth_scalar current_vector_mass_zeroth_value expr0 mul1r.
  exact:lexx.
- exact:(@mass_pushforward_bound R h2 X Y BX BY hBX hBY m
    (@coordinate_basis R m) (@coordinate_basisP R m) f L hL k.+1 (ltn0Sn k)
    (@comass R h2 X BX hBX m (@coordinate_basis R m) (@coordinate_basisP R m) k.+1 (ltn0Sn k))
    (@comass R h2 Y BY hBY n (@coordinate_basis R n) (@coordinate_basisP R n) k.+1 (ltn0Sn k))
    (@comassP R h2 X BX hBX m (@coordinate_basis R m) (@coordinate_basisP R m) k.+1 (ltn0Sn k))
    (@comassP R h2 Y BY hBY n (@coordinate_basis R n) (@coordinate_basisP R n) k.+1 (ltn0Sn k))
    x (@current_vector_mass R h2 m k.+1 x)
    (@current_vector_mass R h2 n k.+1 (exterior_power_map f k.+1 x))
    (@massP R h2 X BX hBX m (@coordinate_basis R m) (@coordinate_basisP R m) k.+1 (ltn0Sn k) x)
    (@massP R h2 Y BY hBY n (@coordinate_basis R n) (@coordinate_basisP R n) k.+1 (ltn0Sn k)
      (exterior_power_map f k.+1 x))).
Qed.
End CurrentExteriorOperatorMassBound.

Section CurrentHomotopyMassIntegrandBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation N d := (@current_vector_mass R h2 n d).

(** Source for [current_first_vector_mass]: the actual
    degree-one mass equals the ordinary Euclidean norm,
    supporting the original velocity factor in Federer
    4.1.9, p. 364, by 1.8.1, p. 38. *)
Theorem current_first_vector_mass (v:Y):N 1%N (exterior_first_inclusion Y v)=NY v.
Proof.
have hSimple:simple (exterior_first_inclusion Y v).
  exists [tuple v];exact:exterior_first_word.
have hEqual:=@simple_mass_euclidean R h2 Y (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
  1%N (ltn0Sn 0) (@current_form_comass R h2 n 1%N)
  (@current_positive_comass_laws R h2 n 1%N (ltn0Sn 0))
  (exterior_first_inclusion Y v) (N 1%N (exterior_first_inclusion Y v)) hSimple
  (@current_positive_mass_laws R h2 n 1%N (ltn0Sn 0) (exterior_first_inclusion Y v)).
by rewrite exterior_first_norm in hEqual.
Qed.

(** Source for [current_homotopy_mass_integrand_bound]: the
    original velocity wedged with the actual spatial
    exterior image has mass at most |v| ||F||^j mass(eta),
    supporting Federer 4.1.9, p. 364. The estimate
    permits every multivector eta, including degree zero. *)
Theorem current_homotopy_mass_integrand_bound j (F:{linear X->Y}) L
    (hL:is_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) F L)
    (v:Y) (eta:exterior_power X j):
  N (1+j) (exterior_product (exterior_first_inclusion Y v) (exterior_power_map F j eta))<=
    NY v*L^+j*@current_vector_mass R h2 m j eta.
Proof.
apply:(le_trans (@current_exterior_product_mass_bound R h2 n 1%N j
  (exterior_first_inclusion Y v) (exterior_power_map F j eta))).
rewrite current_first_vector_mass -mulrA.
exact:(ler_wpM2l (inner_norm_nonnegative (@euclidean_inner_productP R n) v)
  (@current_exterior_operator_mass_bound R h2 m n F L hL j eta)).
Qed.
End CurrentHomotopyMassIntegrandBound.
