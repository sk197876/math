(** Federer (1969), 3.4.8(11), pp. 334–335:
    the actual prepared tail equations and original
    prefix norms supply the full nested finite
    neighbourhood argument. The coefficient estimates and
    radius sequence are proved local existence witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology NormAnalyticUP
  AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives AnalyticPrefixCoordinatesSealed AnalyticRotatedGermIdeal
  OrthonormalFamilies AnalyticPreparedTailUP AnalyticPreparedTailRootControl AnalyticPrefixNormFamily
  AnalyticPrefixNormStep NestedPrefixFiniteNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ActualNeighbourhood.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hON:orthonormal_family B e.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation Y:=(fun j:'I_n=>R_n R j).
Local Notation NY:=(fun j:'I_n=>inner_norm (@euclidean_inner_productP R j)).
Local Notation hNY:=(fun j:'I_n=>inner_norm_real_norm (@euclidean_inner_productP R j)).
Variable I:set (@analytic_germ_ring R X NX hNX 0).
Variable g:@orthogonal_group R X B hB n e he.
Variable m:nat.
Variable degree:'I_n->nat.
Variable U:forall j:'I_n,set (Y j).
Variable b:forall j:'I_n,'I_(degree j)->@analytic_representative_type R (Y j) (NY j) (hNY j) 0.
Variable f:'I_n->@analytic_representative_type R X NX hNX 0.

Hypothesis hLaws:@is_analytic_prepared_reduction_tail R X B hB n e he omega I g m degree U b f.
Local Notation Top:=(Topological.clone (real_norm_metric_space hNX) _).

(** Source for [analytic_prepared_finite_neighbourhood]:
    the actual original finite-component neighbourhood
    in 3.4.8(11), pp. 334–335.
    Prepared equations are needed only inside the
    selected original closed ball. The base component
    count is the preceding lower-dimensional induction input. *)
Theorem analytic_prepared_finite_neighbourhood (hMN:(m<=n)%N) (D:set X) (r:R):
  0<r ->
  (forall j:'I_n,(m<=j)%N ->forall x,D x ->NX x<=r ->
    analytic_representative_value (f j) x = 0) ->
  (forall s:R,0<s ->s<=r ->finite_set (@connected_component Top
      (D `&` [set x|inner_norm (@euclidean_inner_productP R m)
        (@AnalyticPrefixCoordinates.projection R X n omega m hMN x)<s]) @`
      (D `&` [set x|inner_norm (@euclidean_inner_productP R m)
        (@AnalyticPrefixCoordinates.projection R X n omega m hMN x)<s]))) ->
  exists V:set X,@open Top V /\ V 0 /\
    @closure Top V `<=` [set x|NX x<=r] /\
    finite_set (@connected_component Top (D `&` V) @` (D `&` V)).
Proof.
move=>hr hVanish hBaseFinite.
have [q [hQ [hContinuous [hZero hFull]]]]:=@analytic_prefix_norm_family_exists R X B hB n e he hON omega hDual.
pose a:=fun j (x:X)=>if pselect (j<n)%N is left hJN then `|omega (Ordinal hJN) x| else 0.
have hA j (hj:(j<n)%N) x:a j x = `|omega (@Ordinal n j hj) x|.
  rewrite /a;case:(pselect (j<n)%N)=>h.
  - have hIndex:(@Ordinal n j h) = Ordinal hj by apply:val_inj.
    by rewrite hIndex.
  - exfalso;exact:h hj.
have hStep j (hj:(m<=j<n)%N) x (hx:D x):q j.+1 x<=q j x+a j x.
  pose hJN:=leq_trans (leqnSn j) (andP hj).2.
  rewrite (hQ j hJN x) (hQ j.+1 (andP hj).2 x) (hA j (andP hj).2 x).
  exact:(@analytic_prefix_norm_step R X n omega j hJN (andP hj).2
    (@AnalyticPrefixCoordinates.projection R X n omega j hJN)
    (@AnalyticPrefixCoordinates.projection R X n omega j.+1 (andP hj).2)
    (@AnalyticPrefixCoordinates.projection_laws R X n omega j hJN)
    (@AnalyticPrefixCoordinates.projection_laws R X n omega j.+1 (andP hj).2) x).
pose D':set X:=D `&` [set x|NX x<=r].
have hEquations (j:'I_n) (hj:(m<=j)%N) x (hx:D' x):analytic_representative_value (f j) x = 0.
  exact:hVanish j hj x hx.1 hx.2.
have hControl j (hj:(m<=j<n)%N) t (ht:0<t):exists s:R,0<s /\s<t/2 /\
    forall x,D x ->q n x<=r ->q j x<=s ->a j x<t/2.
  pose jj:'I_n:=Ordinal (andP hj).2.
  have [s [hs [hSmall hRoot]]]:=@analytic_prepared_tail_root_control R X B hB n e he omega
    I g m degree U b f hLaws D' hEquations jj (andP hj).1 t ht.
  exists s;split;first exact:hs.
  split;first exact:hSmall.
  move=>x hDx hNx hPx;rewrite (hA j (andP hj).2 x).
  have hNX:NX x<=r by move:hNx;rewrite hFull.
  have hDPrime:D' x by split.
  have hRootAt:=hRoot x hDPrime.
  have hPrefix:=hPx.
  rewrite (hQ (jj:nat) (leq_trans (leqnSn (jj:nat)) (ltn_ord jj)) x) in hPrefix.
  exact:(hRootAt hPrefix).
have hBase s (hs:0<s) (hSR:s<=r):finite_set (@connected_component Top
    (D `&` [set x|q m x<s]) @` (D `&` [set x|q m x<s])).
  have hSet:(D `&` [set x|q m x<s]) = (D `&` [set x|inner_norm (@euclidean_inner_productP R m)
      (@AnalyticPrefixCoordinates.projection R X n omega m hMN x)<s]).
    apply/seteqP;split.
    - move=>x [hx hSmall];split;first exact:hx.
      change (is_true (inner_norm (@euclidean_inner_productP R m)
        (@AnalyticPrefixCoordinates.projection R X n omega m hMN x)<s)).
      by rewrite -(hQ m hMN x).
    - move=>x [hx hSmall];split;first exact:hx.
      change (is_true (q m x<s));by rewrite (hQ m hMN x).
  rewrite hSet;exact:hBaseFinite s hs hSR.
have [epsilon [hLast [hPositive [hOpen [hOrigin [hClosed hFinite]]]]]]:=
  @nested_prefix_finite_neighbourhood R Top n m hMN 0 D q a r hr hContinuous
    (fun j _=>hZero j) hStep hControl hBase.
exists [set x|forall j:'I_n.+1,(m<=j)%N ->q j x<epsilon j].
split;first exact:hOpen.
split;first exact:hOrigin.
split;last exact:hFinite.
move=>x hx;have hBound:=hClosed x hx.
change (is_true (q n x<=r)) in hBound.
by rewrite hFull in hBound.
Qed.
End ActualNeighbourhood.
