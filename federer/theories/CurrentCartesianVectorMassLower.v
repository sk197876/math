(** Federer (1969), 4.1.8, p. 361: the original
    binomial lower mass bound follows by choosing the
    original mass-attaining factor covectors. Their block
    product has the printed comass bound, and its pairing
    is exactly the product of the two factor masses. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct EuclideanBlockLinearMaps ExteriorGrading ExteriorMaps
  ExteriorHomogeneousProducts AlternatingForms AlternatingDual AlternatingProduct AlternatingPairing ScalarCoefficients
  CurrentCoefficientNorms CurrentPositiveCoefficientNorms CurrentDualNorm
  CurrentCartesianVectorProduct CurrentCartesianVectorPairing CurrentCartesianCovectorBinomial
  CurrentCartesianBlockMass CurrentExteriorProductMass MassAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianVectorMassLower.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation p := (hom_as_linear (@euclidean_first_block_map R m n)).
Local Notation q := (hom_as_linear (@euclidean_last_block_map R m n)).

(** Source for [current_cartesian_vector_mass_lower_positive]:
    the original product mass is at least the product
    of the factor masses divided by the displayed binomial
    coefficient, supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_vector_mass_lower_positive i j (hi:(0<i)%N) (hj:(0<j)%N)
    (xi:exterior_power X i) (eta:exterior_power Y j):
  @current_vector_mass R h2 m i xi*@current_vector_mass R h2 n j eta<=
    'C(i+j,i)%:R*(@current_vector_mass R h2 (m+n) (i+j)
      (@current_cartesian_vector_product R m n i j xi eta)).
Proof.
have[a [hA hPairA]]:=@mass_attained R h2 X (@euclidean_inner_product R m)
  (@euclidean_inner_productP R m) m (@coordinate_basis R m) (@coordinate_basisP R m)
  i hi (@current_form_comass R h2 m i) (@current_positive_comass_laws R h2 m i hi)
  xi _ (@current_positive_mass_laws R h2 m i hi xi).
have[b [hB hPairB]]:=@mass_attained R h2 Y (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
  j hj (@current_form_comass R h2 n j) (@current_positive_comass_laws R h2 n j hj)
  eta _ (@current_positive_mass_laws R h2 n j hj eta).
pose w:=form_wedge h2 (scalar_bilinear R) (A_m_dual p a) (A_m_dual q b).
pose z:=@current_cartesian_vector_product R m n i j xi eta.
have hPair:pairing z w= @current_vector_mass R h2 m i xi*@current_vector_mass R h2 n j eta.
  rewrite /z /w (@current_cartesian_vector_pairing R h2 m n i j xi eta a b) hPairA hPairB.
  by [].
have hBound:=real_functional_norm_bound (@current_mass_pairing_norm R h2 (m+n) (i+j) z) w.
change (is_true (`|pairing z w|<=@current_vector_mass R h2 (m+n) (i+j) z*
  @current_form_comass R h2 (m+n) (i+j) w)) in hBound.
rewrite hPair (ger0_norm (mulr_ge0
  (real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 m i).1 xi)
  (real_seminorm_nonnegative (@current_vector_mass_real_norm R h2 n j).1 eta))) in hBound.
apply:le_trans hBound _.
have hCovector:=@current_cartesian_unit_covector_binomial R h2 m n i j a b hA hB.
have h:=ler_wpM2l (real_seminorm_nonnegative
  (@current_vector_mass_real_norm R h2 (m+n) (i+j)).1 z) hCovector.
rewrite [X in _<=X]mulrC;exact:h.
Qed.

(** Source for [current_cartesian_vector_mass_lower]: the
    exact original binomial lower estimate in every natural
    pair of degrees, supporting Federer 4.1.8, p. 361.
    Both zero endpoints have equality. *)
Theorem current_cartesian_vector_mass_lower i j
    (xi:exterior_power X i) (eta:exterior_power Y j):
  @current_vector_mass R h2 m i xi*@current_vector_mass R h2 n j eta<=
    'C(i+j,i)%:R*(@current_vector_mass R h2 (m+n) (i+j)
      (@current_cartesian_vector_product R m n i j xi eta)).
Proof.
case:i xi=>[|a] xi.
- rewrite bin0 mul1r /current_cartesian_vector_product current_exterior_product_mass_zero_left.
  by rewrite current_cartesian_first_inclusion_mass current_cartesian_second_inclusion_mass.
- case:j eta=>[|b] eta.
  + have hCoefficient:'C(a.+1+0,a.+1)= 1%N by rewrite addn0 binn.
    have hMass:=@current_exterior_product_mass_zero_right R h2 (m+n) a.+1
      (exterior_power_map (hom_as_linear (@euclidean_first_injection_map R m n)) a.+1 xi)
      (exterior_power_map (hom_as_linear (@euclidean_last_injection_map R m n)) 0%N eta).
    rewrite current_cartesian_first_inclusion_mass current_cartesian_second_inclusion_mass in hMass.
    rewrite hCoefficient mul1r /current_cartesian_vector_product.
    by rewrite hMass.
  + exact:(@current_cartesian_vector_mass_lower_positive a.+1 b.+1 (ltn0Sn a) (ltn0Sn b) xi eta).
Qed.
End CurrentCartesianVectorMassLower.
