(** Supporting Federer (1969), 3.4.8(5), p. 328:
    multiplication adds finite vanishing orders. Reuse the actual
    Leibniz bound already proved for 3.1.11, p. 222 and the
    original germ metric of 3.4.5, p. 319. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm AnalyticGermUP AnalyticGermRing AnalyticGermJetsSealed
  AnalyticGermGrowthUP AnalyticGermProductBound AnalyticGermJetNormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_jets_vanish_below]: the exact original
    finite-order vanishing predicate, supporting Federer 3.4.8(5),
    p. 328. It is stated through actual derivatives of 3.4.5,
    p. 319, without a formal power-series replacement. *)
Definition analytic_germ_jets_vanish_below (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a q (alpha:@analytic_germ_ring R X NX hNX a):Prop:=
  forall k,(k<q)%N ->@AnalyticGermJets.value R X NX hNX a k alpha = 0.

(** Source for [analytic_product_vanishing_jets]: supporting original
    ideal-power and finite-jet connection for Federer 3.4.8(5), p. 328.
    Vanishing below p and q gives vanishing below p+q for the original
    product. The existing actual Leibniz norm bound proves this, including
    order zero and arbitrary original normed source spaces. *)
Theorem analytic_product_vanishing_jets (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a p q
    (alpha beta:@analytic_germ_ring R X NX hNX a):
  analytic_germ_jets_vanish_below p alpha ->
  analytic_germ_jets_vanish_below q beta ->
  analytic_germ_jets_vanish_below (p+q)%N (alpha*beta).
Proof.
move=>hAlpha hBeta k hK.
pose N j:=@ContinuousMultilinear.norm R j X R^o NX (fun z=>`|z|)
  hNX (@scalar_absolute_value_norm R).
have hN j:is_real_norm (N j):=continuous_multilinear_norm_is_norm
  (@scalar_absolute_value_norm R) (@ContinuousMultilinear.laws R j X R^o NX (fun z=>`|z|)
    hNX (@scalar_absolute_value_norm R)).
have hBound:=@analytic_germ_product_jet_bound R X NX hNX a k alpha beta.
have hSum:(\sum_(j<k.+1) ('C(k,k-j))%:R*
    (@analytic_germ_jet_norm R X NX hNX a (k-j)%N alpha*
     @analytic_germ_jet_norm R X NX hNX a j beta)) = 0.
  apply:big1=>j _.
  change (('C(k,k-j))%:R *
    (N (k-j)%N (@AnalyticGermJets.value R X NX hNX a (k-j)%N alpha) *
     N j (@AnalyticGermJets.value R X NX hNX a j beta)) = 0).
  case:(ltnP j q)=>hJ.
  - by rewrite (hBeta j hJ)
      (real_seminorm_zero (hN j).1) !mulr0.
  - have hJK:(j<=k)%N by have hh:=ltn_ord j;by rewrite ltnS in hh.
    have hKP:(k-j<p)%N.
      rewrite ltn_subLR //.
      have hUpper:(p+q<=j+p)%N by rewrite [(p+q)%N]addnC leq_add2r.
      exact:leq_trans hK hUpper.
    by rewrite (hAlpha (k-j)%N hKP)
      (real_seminorm_zero (hN (k-j)%N).1) mul0r mulr0.
rewrite hSum in hBound.
have hZero:@analytic_germ_jet_norm R X NX hNX a k (alpha*beta) = 0.
  apply/eqP;rewrite eq_le (@analytic_germ_jet_norm_nonnegative R X NX hNX a k (alpha*beta)) andbT.
  exact:hBound.
exact:(hN k).2 _ hZero.
Qed.
