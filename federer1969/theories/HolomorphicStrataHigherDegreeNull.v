(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(13), p. 335:
    the complete finite stratification gives a representative
    with zero measure in every degree greater than
    its original dimension. Actual holomorphic charts connect
    the strata to the already proved rectifiability theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import Hom FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness FunctionalHolomorphicSubmanifoldUP FunctionalHolomorphicManifold HolomorphicSubmanifoldRealCoordinates ComplexEuclideanCoordinates
  AnalyticSubmanifoldUP SubmanifoldCountablyRectifiable CountablyRectifiableHigherDegreeNull
  HausdorffMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_strata_higher_degree_null]: the
    H^(2m+1)-null representative in 3.4.8(13), p. 335.
    This supporting result works at every q>2m,
    without a measurability assumption on the original union. *)
Theorem holomorphic_strata_higher_degree_null (R:realType) n m q mu
    (V S:'I_mu->set (coordinate_space (ComplexScalars.C R) n)):
  (m+m<q)%N ->
  (forall i,exists d,(d<=m)%N /\@is_functional_holomorphic_submanifold R n d (V i) (S i)) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+n))) q ((@complex_from_real_coordinate_hom R n) @^-1` (\bigcup_i S i))=0%E.
Proof.
move=>hMQ hStrata.
have hUnion:((@complex_from_real_coordinate_hom R n) @^-1` (\bigcup_i S i)) =
    \bigcup_i ((@complex_from_real_coordinate_hom R n) @^-1` S i).
  apply/seteqP;split=>x [i _ hx];by exists i.
rewrite hUnion.
apply:(@measure_null_countable_union R (inner_metric_space (@euclidean_inner_productP R (n+n)))
  [the choiceType of 'I_mu]
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n+n))) q)
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R (n+n))) q)
  setT (fun i=>(@complex_from_real_coordinate_hom R n) @^-1` S i) (countableP setT))=>i hi.
have [d [hDM hMan]]:=hStrata i.
have hDoubled:(d+d<=m+m)%N:=leq_add hDM hDM.
apply:(@countably_rectifiable_higher_degree_null R (n+n) (d+d) q
  ((@complex_from_real_coordinate_hom R n) @^-1` S i) (leq_ltn_trans hDoubled hMQ)).
apply:(@submanifold_countably_rectifiable R (n+n) (d+d) 1%N
  ((@complex_from_real_coordinate_hom R n) @^-1` S i) (leqnn 1)).
exact:analytic_submanifold_class_one (functional_holomorphic_paired_real_coordinates hMan).
Qed.
