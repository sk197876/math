(** Federer (1969), 3.2.22, p. 260:
    sum the two local integral bounds over all
    source/target chart pairs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality
  NonnegativeSum NonnegativeSumScale TotalCountableNonnegativeIntegral
  TotalScalarCutoff WeightedScalarCutoff DisjointScalarCutoffSeries.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_coarea_integral_comparison]:
    the summation with respect to i and j in
    Federer 3.2.22, p. 260, using 2.4.8,
    p. 84. Independent laws for the density and
    fibre sums suffice to transfer a common finite
    distortion factor through their integrals and sums.
    All geometric laws are proved separately; this
    supporting theorem assumes no sharp coarea equality. *)
Theorem countable_coarea_integral_comparison (R:realType) (X Y I:choiceType)
    (rho:set X->\bar R) (beta:set Y->\bar R) (hr:is_measure rho) (hb:is_measure beta)
    (A:set X) (P:I->set X) (J:X->R) (N:Y->extended_real_line R)
    (Ni:I->Y->extended_real_line R) (c:R):
  countable (@setT I) ->(0<c)%R ->(forall x,(0<=J x)%R) ->
  (forall i y,0<=Ni i y) ->
  measure_almost_everywhere rho [set x|
    nonnegative_sum setT (fun i=>(total_scalar_cutoff (P i) J x)%:E)=(total_scalar_cutoff A J x)%:E] ->
  measure_almost_everywhere beta [set y|nonnegative_sum setT (fun i=>Ni i y)=N y] ->
  (forall i,exists a b,is_measure_subset_integral rho (P i)
      (partial_function_total (fun x=>((J x)%:E:extended_real_line R))) a /\
    is_measure_integral beta (partial_function_total (Ni i)) b /\
    0<=a /\ 0<=b /\ a<=c%:E*b /\ b<=c%:E*a) ->
  exists a b,is_measure_subset_integral rho A
      (partial_function_total (fun x=>((J x)%:E:extended_real_line R))) a /\
    is_measure_integral beta (partial_function_total N) b /\
    0<=a /\ 0<=b /\ a<=c%:E*b /\ b<=c%:E*a.
Proof.
move=>hCount hc hJ hNi hSourceSum hTargetSum hLocal.
have hPair i:exists ab:(\bar R*\bar R)%type,
    is_measure_subset_integral rho (P i) (partial_function_total (fun x=>((J x)%:E:extended_real_line R))) ab.1 /\
    is_measure_integral beta (partial_function_total (Ni i)) ab.2 /\
    0<=ab.1 /\ 0<=ab.2 /\ ab.1<=c%:E*ab.2 /\ ab.2<=c%:E*ab.1.
  have [a [b hData]]:=hLocal i; by exists (a,b).
have [ab hLaws]:=choice hPair.
pose a:=fun i=>(ab i).1.
pose b:=fun i=>(ab i).2.
have hAIntegral i:is_measure_integral rho
    (partial_function_total (fun x=>((total_scalar_cutoff (P i) J x)%:E:extended_real_line R))) (a i).
  exact:(measure_integral_graph_equivalent (@scalar_cutoff_embedding_graph R X (P i) J) (hLaws i).1).
have hAPositive i x:0<=(total_scalar_cutoff (P i) J x)%:E.
  rewrite lee_fin; exact:(nonnegative_scalar_cutoff (P i) hJ x).
have hASeries:=@total_countable_nonnegative_integral R X I rho hr setT
  (fun i x=>((total_scalar_cutoff (P i) J x)%:E:extended_real_line R)) a hCount
  (fun i _ x=>hAPositive i x) (fun i _=>hAIntegral i).
have hAAgreement:measure_almost_everywhere rho
    (partial_function_agreement
      (partial_function_total (fun x=>(nonnegative_sum setT
        (fun i=>(total_scalar_cutoff (P i) J x)%:E):extended_real_line R)))
      (partial_function_total (fun x=>((total_scalar_cutoff A J x)%:E:extended_real_line R)))).
  apply:(measure_almost_everywhere_mono hr _ hSourceSum)=>x hx.
  exists (total_scalar_cutoff A J x)%:E; by split.
have hATotal:=measure_integral_almost_equal hr hASeries hAAgreement.
have hASubset:is_measure_subset_integral rho A
    (partial_function_total (fun x=>((J x)%:E:extended_real_line R))) (nonnegative_sum setT a).
  exact:(measure_integral_graph_equivalent (fun x z=>iff_sym (@scalar_cutoff_embedding_graph R X A J x z)) hATotal).
have hBSeries:=@total_countable_nonnegative_integral R Y I beta hb setT Ni b hCount
  (fun i _ y=>hNi i y) (fun i _=>(hLaws i).2.1).
have hBAgreement:measure_almost_everywhere beta
    (partial_function_agreement
      (partial_function_total (fun y=>(nonnegative_sum setT (fun i=>Ni i y):extended_real_line R)))
      (partial_function_total N)).
  apply:(measure_almost_everywhere_mono hb _ hTargetSum)=>y hy.
  exists (N y); by split.
have hBIntegral:=measure_integral_almost_equal hb hBSeries hBAgreement.
have hANonnegative i (_:setT i):0<=a i:=(hLaws i).2.2.1.
have hBNonnegative i (_:setT i):0<=b i:=(hLaws i).2.2.2.1.
have hAB:nonnegative_sum setT a<=c%:E*nonnegative_sum setT b.
  rewrite -(nonnegative_sum_scale (ltW hc) hBNonnegative).
  apply:nonnegative_sum_mono=>i _; exact:(hLaws i).2.2.2.2.1.
have hBA:nonnegative_sum setT b<=c%:E*nonnegative_sum setT a.
  rewrite -(nonnegative_sum_scale (ltW hc) hANonnegative).
  apply:nonnegative_sum_mono=>i _; exact:(hLaws i).2.2.2.2.2.
exists (nonnegative_sum setT a),(nonnegative_sum setT b).
split; first exact hASubset; split; first exact hBIntegral.
split; first exact:nonnegative_sum_nonnegative; split; first exact:nonnegative_sum_nonnegative.
by split.
Qed.
