(** Federer (1969), 3.1.24, p. 238: geometric
    domination of the homogeneous differential terms on a ball. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP SymmetricForms SymmetricOperatorNorm
  PolynomialTaylorTerms HomogeneousPolynomialDifferentialNorm AnalyticDerivativeTermMajorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [homogeneous_derivative_geometric_bound]: supporting
    the differentiated-series estimate in Federer 3.1.24,
    p. 238. A coefficient form bounded by c^m m!
    gives ||D^i p_m(x)|| <= (2c)^i i! (2cs)^(m-i)
    on the radius-s ball, for i<=m. This uses actual
    coefficient evaluations, the contraction norm comparison,
    and the proved scalar factorial estimate. *)
Lemma homogeneous_derivative_geometric_bound (R:realType)
    (X Y Z:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) m i
    (ev:{ffun 'I_i->X}->Hom Z Y) (ZN:Z->R)
    (hZ:is_continuous_multilinear_space NX NY ev ZN)
    (phi:S_m X Y m) x z c s :
  (i<=m)%N -> 0<=c -> 0<=s -> NX x<=s ->
  (symmetric_operator_norm hNX.1 NY phi<=(c^+m*(m`!)%:R)%:E)%E ->
  (forall u,ev u z= symmetric_taylor_term i phi x [tuple u j | j<i]) ->
  ZN z<=((2*c)^+i*(i`!)%:R)*(2*c*s)^+(m-i).
Proof.
move=>hi hc hs hx hphi he.
have h1:=@homogeneous_polynomial_differential_norm_bound R X Y Z NX NY hNX hNY m i
  ev ZN hZ phi x z (c^+m*(m`!)%:R) hi hphi he.
have hp:=lerXn2r (m-i) (real_seminorm_nonnegative hNX.1 x) hs hx.
have hd:0<=(((m-i)`!)%:R:R)^-1 by rewrite invr_ge0 ler0n.
have hC:0<=c^+m*(m`!)%:R by exact (mulr_ge0 (exprn_ge0 m hc) (ler0n _ _)).
have h2:=ler_wpM2l hC (ler_wpM2r hd hp).
apply: le_trans (le_trans h1 h2) _.
exact (@analytic_derivative_term_majorant R m i c s hi hc hs).
Qed.
