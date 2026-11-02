(** Federer (1969), 3.2.13, p. 251: identify the
    angular specialization and its Gamma product for a coordinate moment. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
From Federer Require Import GrassmannAbbreviations GaussianProductIntegrand SphereCoordinateParameters
  EulerGamma EulerGammaHalfParameters RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [sphere_coordinate_angular_integrand]: the
    specialized coordinate product is |u_i|^t, Federer 3.2.13,
    p. 251, for every real exponent t, with the existing
    convention at zero coordinates. *)
Lemma sphere_coordinate_angular_integrand (R:realType) m (i:'I_m) (t:R) (u:R_n R m):
  gaussian_angular_integrand (sphere_coordinate_parameters i t) u=real_power `|u i| t.
Proof.
have hTwo:(2:R)!= 0 by apply/eqP; lra.
have hFirst:2*((t+1)/2)-1=t.
  by rewrite mulrCA mulfV // mulr1 addrK.
have hOther:2*(1/2:R)-1= 0 by rewrite div1r mulfV // subrr.
rewrite /gaussian_angular_integrand (bigD1 i) //= /sphere_coordinate_parameters eqxx hFirst.
have hRest:(\prod_(j | j!=i) real_power `|u j| (2*(if j==i then (t+1)/2 else 1/2)-1))= 1.
  apply:big1=>j hj; by rewrite (negbTE hj) hOther real_power_zero_exponent.
by rewrite hRest mulr1.
Qed.

(** Source for [sphere_coordinate_gamma_product]: the Gamma
    product in the coordinate-moment specialization equals Gamma((t+1)/2)
    times Gamma(1/2)^(m-1), Federer 3.2.13, p. 251. *)
Lemma sphere_coordinate_gamma_product (R:realType) m (i:'I_m) (t:R) (ht:-1<t)
    (hz:forall j,0<sphere_coordinate_parameters i t j):
  (\prod_j euler_gamma (hz j))=
    euler_gamma (positive_coordinate_moment_parameter ht)*(euler_gamma_half R)^+(m-1).
Proof.
have hFirst:euler_gamma (hz i)=euler_gamma (positive_coordinate_moment_parameter ht).
  move:(hz i); rewrite /sphere_coordinate_parameters eqxx=>hP.
  exact:euler_gamma_proof_irrelevant.
have hOther j:j!=i ->euler_gamma (hz j)=euler_gamma_half R.
  move=>hj; move:(hz j); rewrite /sphere_coordinate_parameters (negbTE hj)=>hP.
  exact:euler_gamma_proof_irrelevant.
rewrite (bigD1 i) //= hFirst.
congr (_*_).
have hEq:(\prod_(j | j!=i) euler_gamma (hz j))=\prod_(j:'I_m | j!=i) euler_gamma_half R.
  apply:eq_bigr=>j hj; exact:hOther j hj.
by rewrite hEq prodr_const cardC1 card_ord -subn1.
Qed.
