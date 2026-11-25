(** Federer (1969), 3.1.24, p. 241: absolute
    convergence of the coordinate series follows from the
    geometric bound in every positive degree. The constant
    coefficient retains its actual, unrestricted norm. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric ScalarNormMetricCompleteness SymmetricForms
  SymmetricMultiIndices SymmetricIndexBounds SymmetricDividedMonomials SymmetricMonomialTuples
  SymmetricOperatorNorm AnalyticCoordinateMajorant NormGeometricSeriesUniform.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_absolute_coordinate_series]: the
    absolute convergence assertion in Federer 3.1.24, p. 241.
    Positive-degree coefficients bounded by c^m m! have an
    absolutely convergent coordinate series whenever c sum |t_i|<1.
    A slightly larger geometric ratio also handles c=0. No
    bound is imposed on the degree-zero coefficient, correcting
    the implicit constant-term bound in the printed estimate. *)
Theorem analytic_absolute_coordinate_series (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    n (v:'I_n->X) (hv:forall i,NX (v i)<=1) (t:'I_n->R)
    (phi:forall m,S_m X Y m) c :
  0<=c -> c*\sum_i `|t i|<1 ->
  (forall m,(1<=m)%N -> (symmetric_operator_norm hNX.1 NY (phi m)<=(c^+m*(m`!)%:R)%:E)%E) ->
  exists B:R,forall eps:R,0<eps -> exists k:nat,forall N,(k<=N)%N ->
    `|(\sum_(m<N) \sum_(a:symmetric_indices n m)
      `|symmetric_scalar_monomial t (symmetric_indices_unbound a)/
        (symmetric_multi_factorial (symmetric_indices_unbound a))%:R|*
      NY (phi m (symmetric_monomial_tuple v a)))-B|<eps.
Proof.
move=>hc hq hphi.
pose cost m:=\sum_(a:symmetric_indices n m)
  `|symmetric_scalar_monomial t (symmetric_indices_unbound a)/
    (symmetric_multi_factorial (symmetric_indices_unbound a))%:R|*
  NY (phi m (symmetric_monomial_tuple v a)).
have hcost m:0<=cost m.
  apply:sumr_ge0=>a _; exact (mulr_ge0 (normr_ge0 _) (real_seminorm_nonnegative hNY.1 _)).
pose q:=c*\sum_i `|t i|.
have hq0:0<=q by apply:mulr_ge0=>//; apply:sumr_ge0=>i _; exact: normr_ge0.
have hq1:q<1:=hq.
pose r:=(q+1)/2.
have hr:0<r<1 by apply/andP; split; rewrite /r; lra.
have hqr:q<=r by rewrite /r; lra.
pose M:=NY (phi 0%N [tuple (0:X) | i<0])+1.
have hzero:0<=NY (phi 0%N [tuple (0:X) | i<0]):=real_seminorm_nonnegative hNY.1 _.
have hM:1<=M by rewrite /M; lra.
have hMN:0<=M:=le_trans ler01 hM.
have hb m:cost m<=r^+m*M.
  case:m=>[|m].
  - rewrite /cost analytic_coordinate_zero_degree_cost expr0 mul1r /M.
    by rewrite lerDl ler01.
  - have h1:=@analytic_coordinate_degree_majorant R X Y NX NY hNX n v hv t m.+1 (phi m.+1) c
      (hphi m.+1 (leq0n m)).
    have h2:=lerXn2r m.+1 hq0 (ltW (andP hr).1) hqr.
    have h3:=ler_wpM2l (exprn_ge0 m.+1 (ltW (andP hr).1)) hM.
    rewrite mulr1 in h3; exact (le_trans h1 (le_trans h2 h3)).
pose S (N:nat) (_:unit):R^o:=\sum_(m<N) cost m.
have hs N (_:unit) (_:True):`|S N.+1 tt-S N tt|<=r^+N*M.
  rewrite /S big_ord_recr /= addrAC subrr add0r (ger0_norm (hcost N)); exact: hb.
have [G [_ [_ hlimit]]]:=@norm_geometric_series_uniform_limit R unit R^o
  (fun z=>`|z|) (scalar_absolute_value_norm R) (@scalar_norm_metric_complete R)
  (fun _=>True) S r M hr hMN hs.
exists (G tt)=>eps heps.
have [k hk]:=hlimit eps heps.
exists k=>N hN; exact (hk N hN tt Logic.I).
Qed.
