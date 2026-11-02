(** Federer (1969), 3.1.24, p. 238: operator
    estimates for the actual differentials of each homogeneous
    coefficient, through the Chapter 1 contraction norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP SymmetricForms SymmetricOperatorNorm
  PolynomialTaylorTerms ContinuousMultilinearSymmetricNorm WhitneyPolynomialDifferenceBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [homogeneous_polynomial_differential_norm_bound]: the
    bound ||D^i p_m(x)|| <= ||phi_m|| |x|^(m-i)/(m-i)!
    in Federer 3.1.24, p. 238, by 1.10.4–5,
    pp. 46–48. The input z represents the actual
    differential through its already proved contraction formula;
    equality of the Chapter 1 and Chapter 3 norms transfers
    the bound without referring to a construction. *)
Lemma homogeneous_polynomial_differential_norm_bound (R:realType)
    (X Y Z:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) m i
    (ev:{ffun 'I_i->X}->Hom Z Y) (ZN:Z->R)
    (hZ:is_continuous_multilinear_space NX NY ev ZN)
    (phi:S_m X Y m) x z C :
  (i<=m)%N -> (symmetric_operator_norm hNX.1 NY phi<=C%:E)%E ->
  (forall u,ev u z= symmetric_taylor_term i phi x [tuple u j | j<i]) ->
  ZN z<=C*(NX x^+(m-i)/((m-i)`!)%:R).
Proof.
move=>hi hC he.
have ht t:symmetric_taylor_term i phi x t= ev [ffun j=>tnth t j] z.
  rewrite he.
  congr (symmetric_taylor_term i phi x _).
  apply: eq_from_tnth=>j; by rewrite tnth_mktuple ffunE.
have hn:=@continuous_multilinear_symmetric_norm R i X Y Z NX NY hNX hNY ev ZN hZ
  z (symmetric_taylor_term i phi x) ht.
have hh:=@symmetric_taylor_term_operator_bound R X Y NX NY hNX hNY m i hi phi x C hC.
by rewrite hn lee_fin in hh.
Qed.

(** Source for [homogeneous_polynomial_differential_above_degree]: the
    zero terms m<i in the differentiated series in Federer
    3.1.24, p. 238. Their representing continuous multilinear
    elements vanish by extensionality and the established contraction
    formula, as required by 3.1.11, p. 221. *)
Lemma homogeneous_polynomial_differential_above_degree (R:realType)
    (X Y Z:lmodType R) (NX:X->R) (NY:Y->R) m i
    (ev:{ffun 'I_i->X}->Hom Z Y) (ZN:Z->R)
    (hZ:is_continuous_multilinear_space NX NY ev ZN)
    (phi:S_m X Y m) x z :
  (m<i)%N ->
  (forall u,ev u z= symmetric_taylor_term i phi x [tuple u j | j<i]) -> z= 0.
Proof.
move=>hi he; apply: (continuous_multilinear_extensional hZ)=>u.
by rewrite he (symmetric_taylor_term_above_degree _ x hi) sform_zeroE linear0.
Qed.
