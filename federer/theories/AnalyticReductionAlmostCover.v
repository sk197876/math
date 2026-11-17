(** Federer (1969), 3.4.8(13), p. 335:
    the union of all original E_m contains Haar
    almost every rotation. Combine exactly the exceptional
    differences proved null in (7) and (9).
    A least B-tail proves the required finite covering. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed IsotropyGroupTopology HaarIntegralUP CompactGroupHaarNormalisation
  AnalyticGermRing CommutativeIdealUP AnalyticReductionActual AnalyticReductionLociUP
  AnalyticReductionHaarDifference AnalyticReductionHaarSuffixDifference ReductionTailCover
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AlmostCover.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j)=if i==j then 1 else 0.
Local Notation G:=(@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Variable I:set G.
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he)
  O mulO invO unitO.
Local Notation A:=(@analytic_reduction_actual_A R X B hB n e he omega I).
Local Notation Bj:=(@analytic_reduction_actual_B R X B hB n e he omega I).
Local Notation C:=(@analytic_reduction_actual_C R X B hB n e he omega I).
Local Notation E:=(@analytic_reduction_actual_E R X B hB n e he omega I).

(** Source for [analytic_prime_reductions_almost_cover]: the
    complement of the original union E_0 through E_n
    is Haar null, 3.4.8(13), p. 335.
    Both zero and full prefixes remain. The proof
    adds no measurability or generic-direction premise. *)
Theorem analytic_prime_reductions_almost_cover (theta:set O->\bar R):
  is_prime_commutative_ideal I ->is_normalised_haar_measure mulO theta ->
  measure_almost_everywhere theta (\bigcup_m E m).
Proof.
move=>hPrime hTheta.
have [lambda [hLambda hMeasure hRepresentation hRegular]]:=hTheta.1.
pose N1:set O:=\bigcup_(j in @setT 'I_n) (A (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) `\` Bj j).
pose N2:set O:=\bigcup_(m in @setT 'I_n) ([set g|forall j:'I_n,(m<=j)%N ->Bj j g] `\` C m).
have hN1:theta N1=0%E.
  have hEach (j:'I_n) (hj:setT j):theta (A (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) `\` Bj j)=0%E.
    exact:(@analytic_reduction_A_minus_B_haar_null R X B hB n e he hON omega hDual
      I hPrime.1 hPrime.2.1 j mulO invO unitO hO theta hTheta).
  exact (@measure_null_countable_union R (Choice.clone O _) [the choiceType of 'I_n]
    theta hMeasure setT (fun j:'I_n=>A (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) `\` Bj j)
    (countableP setT) hEach).
have hN2:theta N2=0%E.
  have hEach (m:'I_n) (hm:setT m):theta ([set g|forall j:'I_n,(m<=j)%N ->Bj j g] `\` C m)=0%E.
    exact:(@analytic_reduction_B_minus_C_haar_null R X B hB n e he hON omega hDual
      I m mulO invO unitO hO theta hPrime hTheta).
  exact (@measure_null_countable_union R (Choice.clone O _) [the choiceType of 'I_n]
    theta hMeasure setT (fun m:'I_n=>[set g|forall j:'I_n,(m<=j)%N ->Bj j g] `\` C m)
    (countableP setT) hEach).
have hNull:=measure_null_union hMeasure hN1 hN2.
have hBadSubset:(~` (\bigcup_m E m)) `<=` N1 `|` N2.
move=>g hNotCovered.
apply:contrapT=>hOutside;apply:hNotCovered.
have hLoci:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have hA0:~A ord0 g.
  by move/(analytic_reduction_A_membership hLoci ord0 g)=>[hPositive _];rewrite ltn0 in hPositive.
have hAB (j:'I_n):A (@Ordinal n.+1 (j:nat).+1 (ltn_ord j)) g ->Bj j g.
  move=>hA;apply:contrapT=>hNot;apply:hOutside;left;exists j;first exact:Logic.I.
  by split.
have hBC (m:'I_n):(forall j:'I_n,(m<=j)%N ->Bj j g) ->C m g.
  move=>hTail;apply:contrapT=>hNot;apply:hOutside;right;exists m;first exact:Logic.I.
  by split.
have [m hEm]:=@reduction_tail_cover n O A E Bj C g hA0
  (fun m=>analytic_reduction_E_membership hLoci m g)
  (analytic_reduction_E_last_membership hLoci g) hAB hBC.
by exists m.
exact (@measure_null_subset R (Choice.clone O _) theta hMeasure
  (~` (\bigcup_m E m)) (N1 `|` N2) hBadSubset hNull).
Qed.
End AlmostCover.
