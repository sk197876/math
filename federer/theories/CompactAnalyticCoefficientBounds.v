(** Federer (1969), 3.4.8(10), p. 332:
    compact prefix sets away from delta=0
    have the original common coefficient and
    inverse-denominator bounds. Reuse analytic
    reciprocal composition and compact continuity bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric NormBoundedLinearTopology NormDifferentialUP NormClassOneUP NormRegularity
  NormAnalyticUP NormAnalyticLocal NormAnalyticOperations NormClassZeroNonzeroLocus
  ScalarReciprocalAnalytic NormCompactFunctionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_analytic_coefficient_bounds]:
    choose one M with |delta|>=1/M
    and sum_i |b_(i,j)|<=M on
    the original compact prefix set,
    3.4.8(10), p. 332. Empty
    compact sets and finite coefficient families
    remain; no global boundedness is imposed. *)
Theorem compact_analytic_coefficient_bounds (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (U C:set Y) (delta:Y->R)
    (index:finType) k (b:index->'I_k->Y->R):
  compact [set y:real_norm_metric_space hNY|C y] ->
  C `<=` U ->(forall y,C y ->delta y!=0) ->
  @norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY (@scalar_absolute_value_norm R) U delta ->
  (forall j i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY
    (@scalar_absolute_value_norm R) U (b j i)) ->
  exists M:R,0<M /\forall y,C y ->M^-1<=`|delta y| /\
    forall j,\sum_(i<k) `|b j i y|<=M.
Proof.
move=>hCompact hCU hNonzero hDelta hB.
pose V:set Y:=fun y=>U y /\delta y!=0.
have hDeltaZero:=norm_class_continuous (norm_analytic_class_all_orders hDelta 0%N).
have hVOpen:=@norm_class_zero_nonzero_locus_open R Y R^o NY (fun t:R^o=>`|t|) hNY
  (@scalar_absolute_value_norm R) U delta hDeltaZero.
have hV y (hy:V y):norm_domain_interior NY V y.
  have hNeighbourhood:=hVOpen;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R Y NY hNY V y).2 (hNeighbourhood y hy)).
have hCV:C `<=` V by move=>y hy;split;[exact:hCU y hy|exact:hNonzero y hy].
have hVU:V `<=` U by move=>y hy;exact:hy.1.
have hDeltaV:=@norm_analytic_open_restriction R Y R^o NY (fun t:R^o=>`|t|) hNY
  (@scalar_absolute_value_norm R) U V delta hVU hV hDelta.
have hInverse:=@norm_analytic_compose_on R Y R^o R^o NY (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
  hNY (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) V [set t:R^o|t!=0]
  delta (fun t:R^o=>t^-1) (fun y hy=>hy.2) hDeltaV (@scalar_reciprocal_analytic R).
have [K [hK hInverseBound]]:=@norm_class_zero_compact_bounded R Y R^o NY (fun t:R^o=>`|t|)
  hNY (@scalar_absolute_value_norm R) V C (fun y=>(delta y)^-1) hCompact hCV
  (norm_class_continuous (norm_analytic_class_all_orders hInverse 0%N)).
have hExists (q:(index*'I_k)%type):exists M:R,0<M /\forall y,C y ->`|b q.1 q.2 y|<=M.
  exact:(@norm_class_zero_compact_bounded R Y R^o NY (fun t:R^o=>`|t|) hNY
    (@scalar_absolute_value_norm R) U C (b q.1 q.2) hCompact hCU
    (norm_class_continuous (norm_analytic_class_all_orders (hB q.1 q.2) 0%N))).
have [c hC]:=choice hExists.
pose mass:=\sum_(j:index) \sum_(i<k) c (j,i).
have hMass:0<=mass.
  apply:sumr_ge0=>j _;apply:sumr_ge0=>i _;exact:ltW (hC (j,i)).1.
pose M:=K+mass+1.
have hM:0<M by rewrite /M;lra.
have hKM:K<=M by rewrite /M;lra.
have hMassM:mass<=M by rewrite /M;lra.
exists M;split;first exact:hM.
move=>y hy;split.
- have hDeltaPositive:0<`|delta y| by rewrite normr_gt0;exact:hNonzero y hy.
  have hInv:`|delta y|^-1<=M.
    have h:=hInverseBound y hy.
    change (is_true (`|(delta y)^-1|<=K)) in h.
    rewrite normfV in h;exact:le_trans h hKM.
  have hDeltaNormNonzero:`|delta y|!=0 by rewrite normr_eq0;exact:hNonzero y hy.
  have hMNonzero:M!=0 by rewrite (gt_eqF hM).
  have hProduct:1<=M*`|delta y|.
    have h:=ler_wpM2r (ltW hDeltaPositive) hInv.
    by rewrite (mulVf hDeltaNormNonzero) in h.
  by rewrite -(ler_pM2l hM) (mulfV hMNonzero).
- move=>j.
  have hRow:(\sum_(i<k) c (j,i))<=mass.
    rewrite /mass (bigD1 j) //= lerDl.
    apply:sumr_ge0=>l _;apply:sumr_ge0=>i _;exact:ltW (hC (l,i)).1.
  apply:(le_trans _ (le_trans hRow hMassM)).
  apply:ler_sum=>i _;exact:(hC (j,i)).2 y hy.
Qed.
