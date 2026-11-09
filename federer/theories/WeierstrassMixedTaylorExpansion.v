(** Federer (1969), 3.4.6, pp. 322–323: the
    original total-degree grouping of the double series
    converges uniformly to the original analytic function
    on an actual neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormClassZeroTopology
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormHigherDifferentialLocal NormHigherDifferentialUnique NormAnalyticUP NormAnalyticDiagonal NormAnalyticTaylor
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermJetsSealed WeierstrassTransverseUP
  WeierstrassCoefficientUP WeierstrassGroupedUP WeierstrassCoefficientGrouping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_mixed_taylor_expansion]: the
    original analytic representative is the sum of its
    original split coefficients, grouped by total degree,
    in the displayed expansion of 3.4.6, pp. 322–323.
    Actual Taylor convergence on one neighbourhood proves
    the assertion; no infinite-sum identity is assumed. *)
Theorem weierstrass_mixed_taylor_expansion (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (v:X)
    (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (f:analytic_representative_type hNX (0:X)) (q:nat->nat->K->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  (forall i j,is_weierstrass_split_coefficient (analytic_germ f) v inclusion i j (q i j)) ->
  exists U:set X,U 0 /\open (U:set (real_norm_metric_space hNX)) /\
    forall epsilon:R,0<epsilon ->exists n:nat,forall M,(n<=M)%N ->forall x,U x ->
      `|analytic_representative_value f x-
        \sum_(m<M.+1) \sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x)|<epsilon.
Proof.
move=>hSplit hQ.
pose N:=fun t:R^o=>`|t|.
pose hN:=@scalar_absolute_value_norm R.
pose Z i:=@ContinuousMultilinear.space R i X R^o NX N hNX hN.
pose ev i:=@ContinuousMultilinear.evaluation R i X R^o NX N hNX hN.
pose NZ i:=@ContinuousMultilinear.norm R i X R^o NX N hNX hN.
pose hZ i:=@ContinuousMultilinear.laws R i X R^o NX N hNX hN.
pose F:=analytic_representative_value f.
pose alpha:=analytic_germ f.
have hGrouped:=@weierstrass_original_coefficient_grouping R X K NX NK hNX v xi inclusion projection alpha q hSplit hQ.
have hTaylor:=@norm_diagonal_analytic_taylor R X R^o NX N hNX hN setT F 0
  (@norm_analytic_diagonal R X R^o NX N hNX hN setT F 0 (analytic_representative_analytic f)).
have [U [ha [hUT [hSmooth [D [hD hLimit]]]]]]:=hTaylor.
have hOpen x (hx:U x):norm_domain_interior NX U x:=((hSmooth 0%N).1 x hx).1.
have hDerivative m:D m=@AnalyticGermJets.value R X NX hNX 0 m alpha.
  have hFull:=(@norm_higher_differential_open_restriction R X R^o NX N hNX hN Z ev NZ hZ
    m setT U F hUT hOpen 0 ha (D m)).2 (hD m).
  exact:(@norm_higher_differential_unique R X R^o NX N hNX hN Z ev NZ hZ setT F m 0 _ _
    hFull (@AnalyticGermJets.laws R X NX hNX 0 m alpha f (erefl _))).
have hTerm m x:((m`!)%:R)^-1*:ev m [ffun _:'I_m=>x-0] (D m)=
    \sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x).
  rewrite subr0 hDerivative.
  change (((m`!)%:R:R)^-1*ev m [ffun _:'I_m=>x]
    (@AnalyticGermJets.value R X NX hNX 0 m alpha)=
    \sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x)).
  exact:esym (hGrouped m x).
exists U;split;first exact:ha.
split.
- exact:(@norm_class_zero_domain_open R X R^o NX N hNX U F
    (norm_class_continuous (hSmooth 0%N))).
- move=>epsilon hEpsilon;have [n hBound]:=hLimit epsilon hEpsilon.
  exists n=>M hM x hx.
  have hSum:(\sum_(m<M.+1) ((m`!)%:R)^-1*:ev m [ffun _:'I_m=>x-0] (D m))=
      \sum_(m<M.+1) \sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x).
    apply:eq_bigr=>m _;exact:hTerm m x.
  rewrite -hSum;exact:hBound M hM x hx.
Qed.
