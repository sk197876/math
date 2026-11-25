(** Federer (1969), 3.2.13, p. 250: the multivariate
    Gaussian power is a product of one-dimensional factors. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  GammaSquareIntegrand RealPower RealExponentialUP RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [gaussian_angular_integrand]: the coordinate
    product inside the definition of 2B(z), Federer 3.2.13,
    p. 250. The same expression is used on the whole space. *)
Definition gaussian_angular_integrand (R:realType) m (z:'I_m->R) (x:R_n R m):R:=
  \prod_j real_power `|x j| (2*z j-1).

(** Source for [gaussian_product_integrand]: the multivariate
    integrand exp(-|x|^2) times the coordinate powers,
    Federer 3.2.13, p. 250. *)
Definition gaussian_product_integrand (R:realType) m (z:'I_m->R) (x:R_n R m):R:=
  RealExponential.exponential (-(inner_norm (@euclidean_inner_productP R m) x)^+2)*
  gaussian_angular_integrand z x.

(** Source for [real_exponential_finite_sum]: the elementary
    exponential product identity used in Cartesian Fubini,
    supporting Federer 3.2.13, p. 250. *)
Lemma real_exponential_finite_sum (R:realType) (J:finType) (f:J->R):
  RealExponential.exponential (\sum_j f j)=\prod_j RealExponential.exponential (f j).
Proof.
elim/big_rec2: _=>[|j a b _ hab].
- exact:real_exponential_zero (@RealExponential.laws R).
- by rewrite (real_exponential_add (@RealExponential.laws R)) hab.
Qed.

(** Source for [gaussian_product_factorization]: the pointwise
    factorization justifying multiplication of the Gamma integrals
    by Fubini, Federer 3.2.13, p. 250. *)
Lemma gaussian_product_factorization (R:realType) m (z:'I_m->R) (x:R_n R m):
  gaussian_product_integrand z x=\prod_j gamma_square_integrand (z j) (x j).
Proof.
rewrite /gaussian_product_integrand /gaussian_angular_integrand inner_norm_sqr
  /euclidean_inner_product.
have hSum:-(\sum_j x j*x j)=\sum_j -(x j)^+2.
  have he:(\sum_j x j*x j)=\sum_j (x j)^+2.
    apply:eq_bigr=>j _; by rewrite expr2.
  by rewrite he sumrN.
rewrite hSum real_exponential_finite_sum -big_split.
apply:eq_bigr=>j _; by rewrite /gamma_square_integrand.
Qed.

(** Source for [gaussian_angular_nonnegative]: nonnegativity of
    the angular coordinate product defining B, Federer 3.2.13,
    p. 250, including negative exponents under the stated zero convention. *)
Lemma gaussian_angular_nonnegative (R:realType) m (z:'I_m->R) (x:R_n R m):
  0<=gaussian_angular_integrand z x.
Proof. apply:prodr_ge0=>j _; exact:real_power_nonnegative. Qed.
