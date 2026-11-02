(** Federer (1969), 3.2.13, pp. 250–251: the angular
    B function is the Gamma product divided by Gamma of the sum. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EulerBeta EulerGamma GammaAngularEvaluation
  MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euler_beta_gamma_formula]: B(z)=product(Gamma(z_j))
    divided by Gamma(sum(z)), the conclusion of Federer 3.2.13,
    pp. 250–251. The B value is the opaque angular function,
    not a definition by this quotient. *)
Theorem euler_beta_gamma_formula (R:realType) m (hm:(0<m)%N) (z:R_n R m) (hz:forall j,0<z j):
  euler_beta hm hz=(\prod_j euler_gamma (hz j))/euler_gamma (positive_coordinate_sum hm hz).
Proof.
have hEq:=EFin_inj (measure_integral_unique (euler_beta_integral hm hz)
  (@gamma_angular_integral_evaluation R m z hz hm)).
nra.
Qed.

(** Source for [gamma_product_euler_beta]: product(Gamma(z_j))=
    Gamma(sum(z))B(z), the multivariate conclusion in Federer
    3.2.13, p. 250. All denominator positivity has been proved. *)
Corollary gamma_product_euler_beta (R:realType) m (hm:(0<m)%N) (z:R_n R m) (hz:forall j,0<z j):
  (\prod_j euler_gamma (hz j))=euler_gamma (positive_coordinate_sum hm hz)*euler_beta hm hz.
Proof.
rewrite euler_beta_gamma_formula mulrC divfK //.
exact:lt0r_neq0 (euler_gamma_positive (positive_coordinate_sum hm hz)).
Qed.
