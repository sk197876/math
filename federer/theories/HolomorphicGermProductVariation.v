(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: variation
    of the actual product derivative is controlled by finitely
    many actual coefficient differences, using the Leibniz
    formula of 3.1.11, p. 222. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP HolomorphicGermUP HolomorphicGermSealed HolomorphicGermRing
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  HolomorphicGermJetsSealed HolomorphicGermGrowthUP HolomorphicGermJetArithmetic HolomorphicGermJetDifference HolomorphicGermProductBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_product_jet_variation]: the
    actual finite Leibniz estimate for the difference of
    two products, supporting the continuous ring operations
    of 3.4.5, p. 319. *)
Theorem holomorphic_germ_product_jet_variation (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) m
    (alpha beta alpha0 beta0:[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]):
  @holomorphic_germ_jet_norm R X NX hNX a m (alpha*beta-alpha0*beta0)<=
    \sum_(j<m.+1) ('C(m,m-j))%:R*
      (@holomorphic_germ_jet_norm R X NX hNX a (m-j)%N (alpha-alpha0)*@holomorphic_germ_jet_norm R X NX hNX a j beta+
       @holomorphic_germ_jet_norm R X NX hNX a (m-j)%N alpha0*@holomorphic_germ_jet_norm R X NX hNX a j (beta-beta0)).
Proof.
pose N:=@ContinuousMultilinear.norm R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R).
pose hN:=continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
  (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)).
have hIdentity:alpha*beta-alpha0*beta0=(alpha-alpha0)*beta+alpha0*(beta-beta0) by ring.
rewrite hIdentity /holomorphic_germ_jet_norm holomorphic_germ_jet_add.
apply:le_trans (real_seminorm_triangle hN.1 _ _) _.
have hFirst:=@holomorphic_germ_product_jet_bound R X NX hNX a m (alpha-alpha0) beta.
have hSecond:=@holomorphic_germ_product_jet_bound R X NX hNX a m alpha0 (beta-beta0).
apply:le_trans (lerD hFirst hSecond) _.
rewrite -big_split /=;apply:ler_sum=>j _.
by rewrite mulrDr.
Qed.
