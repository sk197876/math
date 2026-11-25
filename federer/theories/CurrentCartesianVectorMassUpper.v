(** Federer (1969), 4.1.8, p. 361: the original
    product coefficient has mass at most the product of
    the factor masses. Both original block inclusions
    preserve mass, and the earlier exterior product bound
    includes both zero degrees. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations ExteriorGrading CurrentCoefficientNorms
  CurrentCartesianVectorProduct CurrentCartesianBlockMass CurrentExteriorProductMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_cartesian_vector_mass_upper]: the
    pointwise original product-density mass bound used in
    the first variation comparison of Federer 4.1.8, p. 361.
    No simplicity assumption or positive-degree restriction
    is required. *)
Theorem current_cartesian_vector_mass_upper (R:realType) (h2:(1+1:R)!=0) m n i j
    (xi:exterior_power (R_n R m) i) (eta:exterior_power (R_n R n) j):
  @current_vector_mass R h2 (m+n) (i+j) (@current_cartesian_vector_product R m n i j xi eta)<=
    @current_vector_mass R h2 m i xi*@current_vector_mass R h2 n j eta.
Proof.
rewrite /current_cartesian_vector_product.
apply:le_trans (@current_exterior_product_mass_bound R h2 (m+n) i j _ _) _.
by rewrite current_cartesian_first_inclusion_mass current_cartesian_second_inclusion_mass.
Qed.
