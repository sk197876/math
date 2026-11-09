(** Federer (1969), 3.4.5, p. 319: variation
    of the actual product derivative is controlled by finitely
    many actual coefficient differences, using the Leibniz
    formula of 3.1.11, p. 222. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermSealed AnalyticGermRing
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  AnalyticGermJetsSealed AnalyticGermGrowthUP AnalyticGermJetArithmetic AnalyticGermJetDifference AnalyticGermProductBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_product_jet_variation]: the
    actual finite Leibniz estimate for the difference of
    two products, supporting the continuous ring operations
    of 3.4.5, p. 319. *)
Theorem analytic_germ_product_jet_variation (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) m
    (alpha beta alpha0 beta0:[the comNzRingType of (@analytic_germ_ring R X NX hNX a)]):
  @analytic_germ_jet_norm R X NX hNX a m (alpha*beta-alpha0*beta0)<=
    \sum_(j<m.+1) ('C(m,m-j))%:R*
      (@analytic_germ_jet_norm R X NX hNX a (m-j)%N (alpha-alpha0)*@analytic_germ_jet_norm R X NX hNX a j beta+
       @analytic_germ_jet_norm R X NX hNX a (m-j)%N alpha0*@analytic_germ_jet_norm R X NX hNX a j (beta-beta0)).
Proof.
pose N:=@ContinuousMultilinear.norm R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R).
pose hN:=continuous_multilinear_norm_is_norm (@scalar_absolute_value_norm R)
  (@ContinuousMultilinear.laws R m X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)).
have hIdentity:alpha*beta-alpha0*beta0=(alpha-alpha0)*beta+alpha0*(beta-beta0) by ring.
rewrite hIdentity /analytic_germ_jet_norm analytic_germ_jet_add.
apply:le_trans (real_seminorm_triangle hN.1 _ _) _.
have hFirst:=@analytic_germ_product_jet_bound R X NX hNX a m (alpha-alpha0) beta.
have hSecond:=@analytic_germ_product_jet_bound R X NX hNX a m alpha0 (beta-beta0).
apply:le_trans (lerD hFirst hSecond) _.
rewrite -big_split /=;apply:ler_sum=>j _.
by rewrite mulrDr.
Qed.
