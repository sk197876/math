(** Federer (1969), 4.1.12, p. 368: the
    boundary of the original interval series has
    infinite mass. Construct bounded smooth endpoint
    witnesses: one at its first N right
    endpoints, zero at every left endpoint and
    at all later right endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  AlternatingForms AlternatingZero CurrentZeroCovectorMaps CurrentSpaces
  DyadicCurrentEndpointArithmetic DyadicEndpointSupportGeometry DyadicCurrentEndpointIndices
  DyadicCurrentEndpointCompact CurrentFiniteIsolatedTest.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DyadicIntervalBoundaryTest.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation DT := (@current_test_space R h2 1%N Full hFull 0%N).
Local Notation value := (@current_test_value R h2 1%N Full hFull 0%N).
Local Notation A := (dyadic_current_endpoint_carrier R).
Local Notation left k := (euclidean_one_embed (dyadic_current_left_endpoint R k)).
Local Notation right k := (euclidean_one_embed (dyadic_current_right_endpoint R k)).

(** Source for [dyadic_interval_boundary_test_exists]:
    an actual original test of scalar range
    [0,1] selects the first N positive
    endpoint atoms and none of the negative
    atoms or later atoms. This proves the
    infinite-mass assertion in Federer 4.1.12,
    p. 368, without assuming endpoint interpolation. *)
Theorem dyadic_interval_boundary_test_exists N:
  exists gamma:DT,
    (forall x,0<=@current_zero_form_coefficient R 1%N (value gamma x)<=1) /\
    (forall j,value gamma (left j)=0) /\
    forall j,value gamma (right j)=@zero_form R X R^o (if (j<N)%N then 1 else 0).
Proof.
pose a (i:'I_N):X:=right (val i).
have hIsolated i:exists W:set X,@open (real_norm_metric_space hNX) W /\W (a i) /\
    forall z,A z->W z->z=a i.
  apply:(@dyadic_current_endpoint_isolated R (a i)).
  - change (dyadic_endpoint_set R (euclidean_one_project (a i))).
    rewrite /a euclidean_one_embedK;exact:dyadic_current_right_endpoint_in_set.
  - move=>hZero.
    have hScalar:=congr1 (@euclidean_one_project R) hZero.
    rewrite /a !euclidean_one_embedK in hScalar.
    have[ha [hab _]]:=@dyadic_current_endpoint_bounds R (val i).
    have hPositive:=lt_trans ha hab.
    by rewrite hScalar ltxx in hPositive.
have[gamma [hRange [hOne hOff]]]:=@current_finite_isolated_test_exists R h2 1%N A 'I_N a hIsolated.
exists gamma;split;first exact:hRange.
split.
- move=>j;apply:(hOff (left j)).
  + change (dyadic_endpoint_set R (euclidean_one_project (left j))).
    rewrite euclidean_one_embedK;exact:dyadic_current_left_endpoint_in_set.
  + move=>[i _ hEqual].
    have hScalar:=congr1 (@euclidean_one_project R) hEqual.
    rewrite /a !euclidean_one_embedK in hScalar.
    exact:(@dyadic_current_opposite_endpoints_distinct R j (val i) (esym hScalar)).
- move=>j;case:(ltnP j N)=>hJN.
  + exact:(hOne (@Ordinal N j hJN)).
  + have hZero:value gamma (right j)=0.
      apply:(hOff (right j)).
      * change (dyadic_endpoint_set R (euclidean_one_project (right j))).
        rewrite euclidean_one_embedK;exact:dyadic_current_right_endpoint_in_set.
      * move=>[i _ hEqual].
        have hScalar:=congr1 (@euclidean_one_project R) hEqual.
        rewrite /a !euclidean_one_embedK in hScalar.
        have hIndex:=@dyadic_current_right_endpoints_injective R (val i) j hScalar.
        have hBad:(j<N)%N by rewrite -hIndex;exact:valP i.
        by have:=leq_ltn_trans hJN hBad;rewrite ltnn.
    rewrite hZero;exact:esym (linear0 (@zero_form R X R^o)).
Qed.
End DyadicIntervalBoundaryTest.
