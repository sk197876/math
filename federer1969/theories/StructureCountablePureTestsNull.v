(** Federer (1969), 3.3.17, pp. 300–301: the original
    countable family of pure test remainders is null. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionMetric
  StructureConeBoundTests StructureRationalConeTests StructurePureDensityTestNull
  RectifiableSetUP PureUnrectifiableLaws MeasureDerivationContext MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_countable_pure_tests_null]: the
    countable-union conclusion in Federer 3.3.17, pp. 300–301.
    Every original test outside the original rectifiable part
    is a subset of the actual pure complement. Proved density-one
    transfer and 3.3.6 make each original test remainder null.
    Four actual countable null unions cover the original union
    remainder. No test or remainder measurability is assumed. *)
Theorem structure_countable_pure_tests_null (R:realType) n m (hmn:(m<=n)%N)
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (D:set (orthogonal_projection_metric_space R n m))
    (B:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_derivation_measure psi ->psi setT< +oo ->countable D ->
  is_purely_measure_m_unrectifiable psi m (setT `\` B) ->
  psi (structure_countable_cone_tests hmn psi D `\` B)= 0.
Proof.
move=>hPsi hFinite hD hPure.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hMeasure:=derivation_measure_law hPsi.
pose T:=[set t:rat|(0<(ratr t:R)<1)%R].
pose M:=[set mu:rat|(0<(ratr mu:R))%R].
pose E:=[set epsilon:rat|(0<(ratr epsilon:R))%R].
pose F q t mu epsilon:=structure_density_cone_test hmn psi q
  (ratr t) (ratr mu) (ratr epsilon) `\` B.
have hNull q t mu epsilon:T t ->M mu ->E epsilon ->psi (F q t mu epsilon)= 0.
  move=>hT hM hE.
  have hSub:F q t mu epsilon `<=` setT `\` B by move=>x [_ hn]; split.
  have hPiecePure:=@pure_unrectifiable_subset R [the metricType R of X] psi m _ _ hSub hPure.
  apply:(@structure_pure_density_test_null R n m hmn psi (F q t mu epsilon)
    q (ratr t) (ratr mu) (ratr epsilon) hPsi hFinite hPiecePure hT (ltW hM) hE).
  by move=>x [hx _].
pose U:=\bigcup_(q in D) \bigcup_(t in T) \bigcup_(mu in M) \bigcup_(epsilon in E) F q t mu epsilon.
have hUNull:psi U= 0.
  apply:(@measure_null_countable_union R [the choiceType of X]
    (orthogonal_projection_metric_space R n m) psi hMeasure D _ hD)=>q hQ.
  apply:(@measure_null_countable_union R [the choiceType of X]
    [the choiceType of (rat:Type)] psi hMeasure T _ (countableP T))=>t hT.
  apply:(@measure_null_countable_union R [the choiceType of X]
    [the choiceType of (rat:Type)] psi hMeasure M _ (countableP M))=>mu hM.
  apply:(@measure_null_countable_union R [the choiceType of X]
    [the choiceType of (rat:Type)] psi hMeasure E _ (countableP E))=>epsilon hE.
  exact:hNull q t mu epsilon hT hM hE.
apply:(@measure_null_subset R [the choiceType of X] psi hMeasure _ U _ hUNull).
move=>x [[q hQ [t hT [mu hM [epsilon hE hx]]]] hn].
exists q; first exact:hQ.
exists t; first exact:hT.
exists mu; first exact:hM.
exists epsilon; first exact:hE.
by split.
Qed.
