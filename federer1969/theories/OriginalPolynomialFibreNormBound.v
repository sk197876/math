(** Federer (1969), 3.4.8(10), p. 332:
    the original polynomial equations bound the
    fibres over compact prefix sets. Apply
    the proved coefficient and coordinate bounds,
    then the existing finite basis expansion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import Hom TensorUP RealNormUP NormMetric LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanCoordinateMetric NormDifferentialUP
  NormClassOneUP NormRegularity NormRegularityOperations NormOpenDomainLaws NormCompactFunctionBound
  NormAnalyticUP CompactAnalyticCoefficientBounds OriginalPolynomialCoordinateBounds
  AnalyticPrefixCoordinatesUP OrdinalCoordinateTail AnalyticPrefixSuffixSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FibreBound.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variables n m:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Hypothesis hMN:(m<=n)%N.
Local Notation Y:=(R_n R m).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation tail:=(ordinal_coordinate_tail_index hMN).
Variable P:Hom X Y.
Hypothesis hP:is_analytic_prefix_projection omega hMN P.
Variable first:'I_(n-m).
Variable k:nat.
Hypothesis hK:(0<k)%N.
Variables U C:set Y.
Variable delta:Y->R.
Variable b0:'I_k->Y->R.
Variable b:'I_(n-m)->'I_k->Y->R.
Variable Z:set X.
Hypothesis hCompact:compact [set y:real_norm_metric_space hNY|C y].
Hypothesis hCU:C `<=` U.
Hypothesis hNonzero:forall y,C y ->delta y!=0.
Hypothesis hDelta:@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY (@scalar_absolute_value_norm R) U delta.
Hypothesis hB0:forall i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY
  (@scalar_absolute_value_norm R) U (b0 i).
Hypothesis hB:forall j i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY
  (@scalar_absolute_value_norm R) U (b j i).
Hypothesis hRoot:forall x,Z x ->
  (omega (tail first) x)^+k+\sum_(i<k) b0 i (P x)*(omega (tail first) x)^+(i:nat) = 0.
Hypothesis hRelations:forall x,Z x ->forall j,j!=first ->
  delta (P x)*omega (tail j) x = \sum_(i<k) b j i (P x)*(omega (tail first) x)^+(i:nat).

(** Source for [original_polynomial_fibre_norm_bound]:
    boundedness of Z intersect p_m inverse(C),
    3.4.8(10), p. 332. Prefix coordinates
    are bounded on C; the monic
    equation and the common denominator bound
    all suffix coordinates. The original supplied
    basis reconstructs the actual source vector. *)
Theorem original_polynomial_fibre_norm_bound:
  exists M:R,0<M /\forall x,Z x ->C (P x) ->NX x<=M.
Proof.
pose index:finType:=[the finType of option 'I_(n-m)].
pose c (j:index) := if j is Some t then b t else b0.
have hCAnalytic j i:@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY
    (@scalar_absolute_value_norm R) U (c j i).
  case:j=>[j|];[exact:hB|exact:hB0].
have [M [hM hBounds]]:=@compact_analytic_coefficient_bounds R Y NY hNY U C delta index k c
  hCompact hCU hNonzero hDelta hCAnalytic.
pose IdY:Hom Y Y:=hom_of_linear (linear_id Y).
have hIdBound:norm_bounded_linear NY NY IdY.
  exists 1;split;first exact:ler01.
  by move=>y;rewrite mul1r.
have hIdClass:=@norm_class_linear R Y Y NY NY hNY hNY setT IdY 0%N
  (fun y _=>@norm_full_domain_interior R Y NY y) hIdBound.
have [B [hBPositive hPrefixBound]]:=@norm_class_zero_compact_bounded R Y Y NY NY hNY hNY
  setT C IdY hCompact (fun y _=>I) (norm_class_continuous hIdClass).
pose D:=Num.max 1 M.
pose T:=M^+2*D^+k.-1.
pose A:=B+D+T.
have hD:0<D by apply:(lt_le_trans ltr01);rewrite /D le_max lexx.
have hT:0<=T by apply:mulr_ge0;[exact:exprn_ge0 _ (ltW hM)|exact:exprn_ge0 _ (ltW hD)].
have hA:0<A by rewrite /A;lra.
have hBA:B<=A by rewrite /A -addrA lerDl;exact:addr_ge0 (ltW hD) hT.
have hDA:D<=A.
  have hDB:D<=B+D by rewrite lerDr;exact:ltW hBPositive.
  apply:(le_trans hDB);by rewrite /A lerDl.
have hTA:T<=A by rewrite /A lerDr;exact:addr_ge0 (ltW hBPositive) (ltW hD).
pose S:=\sum_i NX (e i).
have hS:0<=S by apply:sumr_ge0=>i _;exact:(real_seminorm_nonnegative hNX.1 (e i)).
exists (A*S+1);split;first by have hAS:=mulr_ge0 (ltW hA) hS;lra.
move=>x hx hc.
have hAt:=hBounds (P x) hc.
have hDeltaPositive:0<`|delta (P x)| by rewrite normr_gt0;exact:hNonzero (P x) hc.
have hDeltaNormNonzero:`|delta (P x)|!=0 by rewrite normr_eq0;exact:hNonzero (P x) hc.
have hMNonzero:M!=0 by rewrite (gt_eqF hM).
have hInverse:`|(delta (P x))^-1|<=M.
  rewrite normfV -(ler_pM2r hDeltaPositive) (mulVf hDeltaNormNonzero).
  have h:=ler_wpM2l (ltW hM) hAt.1.
  by rewrite (mulfV hMNonzero) in h.
have hCoordinates:=@original_polynomial_coordinate_bounds R k [the finType of 'I_(n-m)] first
  (fun i=>b0 i (P x)) (fun j i=>b j i (P x)) (delta (P x)) M
  (fun j=>omega (tail j) x) hK hM (@hNonzero (P x) hc) hInverse
  (hAt.2 None) (fun j=>hAt.2 (Some j)) (@hRoot x hx) (@hRelations x hx).
have hAll i:`|omega i x|<=A.
  case:(ltnP (i:nat) m)=>[hSmall|hLarge].
  - pose j:'I_m:=Ordinal hSmall.
    have hIndex:widen_ord hMN j = i by apply:val_inj.
    have hCoordinate:=@euclidean_coordinate_norm_bound R m j (P x).
    rewrite hP hIndex in hCoordinate.
    have hPrefix:=hPrefixBound (P x) hc.
    change (is_true (NY (P x)<=B)) in hPrefix.
    exact:le_trans (le_trans hCoordinate hPrefix) hBA.
  - have [j hIndex]:=@ordinal_coordinate_tail_complete n m hMN i hLarge.
    rewrite -hIndex.
    case hFirst:(j==first).
    + have hJ:j=first:=eqP hFirst;subst j.
      exact:le_trans hCoordinates.1 hDA.
    + have hJ:j!=first by rewrite hFirst.
      exact:le_trans (hCoordinates.2 j hJ) hTA.
have hExpansion:=@analytic_original_given_basis_expansion R X n e he omega hDual x.
have hNorm:NX x<=A*S.
  rewrite {1}hExpansion.
  apply:(le_trans (real_seminorm_sum hNX.1 _)).
  rewrite /S mulr_sumr.
  apply:ler_sum=>i _.
  rewrite (real_seminorm_scale hNX.1).
  change (is_true (`|omega i x|*NX (e i)<=A*NX (e i))).
  exact:(ler_wpM2r (real_seminorm_nonnegative hNX.1 (e i)) (hAll i)).
by apply:(le_trans hNorm);rewrite lerDl ler01.
Qed.
End FibreBound.
