(** Federer (1969), 3.2.13, p. 250: positive-radius
    separation of the Gaussian power into its radial and angular factors. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm GaussianProductIntegrand
  RealPower RealPowerSuccessor RealPowerNaturalHausdorff RealExponentialUP RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_finite_exponent_sum]: multiplication
    of powers of a fixed positive base adds exponents, supporting
    polar separation in Federer 3.2.13, p. 250. *)
Lemma real_power_finite_exponent_sum (R:realType) (J:finType) (r:R) (p:J->R):
  0<r ->real_power r (\sum_j p j)=\prod_j real_power r (p j).
Proof.
move=>hr; elim/big_rec2: _=>[|j a b _ hab].
- exact:real_power_zero_exponent.
- by rewrite real_power_add_exponents_positive // hab.
Qed.

(** Source for [gaussian_radial_factor]: the radial factor
    exp(-r^2)r^(sum(2z_j-1)) before multiplication by r^(m-1),
    Federer 3.2.13, p. 250. *)
Definition gaussian_radial_factor (R:realType) m (z:'I_m->R) (r:R):R:=
  RealExponential.exponential (-r^+2)*real_power r (\sum_j (2*z j-1)).

(** Source for [gaussian_radial_factor_positive]: every positive
    radius has a strictly positive radial factor in the
    Gamma product polar calculation, Federer 3.2.13, p. 250. *)
Lemma gaussian_radial_factor_positive (R:realType) m (z:'I_m->R) (r:R):
  0<r ->0<gaussian_radial_factor z r.
Proof.
move=>hr; apply:mulr_gt0.
- exact:(real_exponential_positive (@RealExponential.laws R) (-r^+2)).
- exact:(@real_power_strictly_positive R r (\sum_j (2*z j-1)) hr).
Qed.

(** Source for [gaussian_angular_dilation]: the homogeneous
    coordinate factor under x=ru in Federer 3.2.13, p. 250.
    Negative exponents and zero coordinates use the existing
    zero-power convention and require no additional exceptional-set premise. *)
Lemma gaussian_angular_dilation (R:realType) m (z:'I_m->R) (r:R) (u:R_n R m):
  0<r ->gaussian_angular_integrand z (r*:u)=
    real_power r (\sum_j (2*z j-1))*gaussian_angular_integrand z u.
Proof.
move=>hr; rewrite /gaussian_angular_integrand real_power_finite_exponent_sum // -big_split.
apply:eq_bigr=>j _.
by rewrite ffunE normrM (ger0_norm (ltW hr)) real_power_product ?(ltW hr) ?normr_ge0.
Qed.

(** Source for [gaussian_polar_separation]: the angular/radial
    factorization on the unit sphere in Federer 3.2.13,
    p. 250, with all coordinate exponents retained. *)
Lemma gaussian_polar_separation (R:realType) m (z:'I_m->R) (r:R) (u:R_n R m):
  0<r ->inner_norm (@euclidean_inner_productP R m) u= 1 ->
  gaussian_product_integrand z (r*:u)=gaussian_radial_factor z r*gaussian_angular_integrand z u.
Proof.
move=>hr hu; rewrite /gaussian_product_integrand inner_normZ (ger0_norm (ltW hr)) hu mulr1
  gaussian_angular_dilation // /gaussian_radial_factor mulrA.
by [].
Qed.
