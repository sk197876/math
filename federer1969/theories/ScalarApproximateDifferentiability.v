(** Federer (1969), 3.1.4, pp. 214–216: the scalar
    almost-everywhere approximate differentiability theorem. The proof
    follows the printed B/C cutoffs, Fubini estimate and coordinate
    telescope; all exceptional-mass bounds are discharged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates BasisInterpolation
  EuclideanInnerProduct InnerNorm InnerMetric EuclideanLebesgueDimensions
  RealNormUP RealMetricBackground PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction ApproximatePartialDerivative ApproximateDifferentialUP
  MeasurableApproximatePartialRepresentative ApproximatePartialUniformCutoffs
  CoordinateMeasurableSliceCutoffs ApproximateCoordinateMassCriterion
  ApproximateCoordinateExceptionalSets FiniteFamilyTwoStageCutoffs
  AlmostEverywhereFromLargeSubsets MeasureUP MeasureAlmostUP
  MeasurableFunctionUP MeasurableGraphEquivalence MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [scalar_approximate_differentiability_from_partials]:
    the last conclusion of Federer 3.1.4, p. 214, proved
    on pp. 214–216 after reducing to the scalar target. The
    first-order map has exactly the approximate partials as basis
    values. Positive source dimension retains the quotient-domain
    convention of 3.1.2, p. 212. *)
Theorem scalar_approximate_differentiability_from_partials (R : realType) n
    (f : R_n R n.+1 -> R^o) :
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n.+1)]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R n.+1)
    (partial_function_total f) ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R n.+1)
    (\bigcap_i partial_function_domain
      (approximate_partial_derivative (scalar_absolute_value_norm R) setT f i))
    [set a | exists L : Hom (R_n R n.+1) [the lmodType R of R^o],
      has_approximate_differential (fun x : R^o=>`|x|) setT f a L /\
      forall i : 'I_n.+1, partial_function_graph
        (approximate_partial_derivative (scalar_absolute_value_norm R) setT f i)
        a (L (@coordinate_basis R n.+1 i))].
Proof.
move=> hf.
pose X := inner_metric_space (@euclidean_inner_productP R n.+1).
pose mu := @euclidean_lebesgue_measure R n.+1.
pose hm := euclidean_lebesgue_is_measure R n.+1.
have hfA : @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] mu
    (partial_function_source_restrict setT (partial_function_total f)).
  apply: (measurable_function_graph_equivalent _ hf)=> x y; by split=> [hy|[_ hy]].
have hchoose : forall i : 'I_n.+1, exists g : X -> R^o,
    @is_measure_measurable_function R [the choiceType of X]
      [the topologicalType of real_line_metric R] mu (partial_function_total g) /\
    forall x v, partial_function_graph
      (approximate_partial_derivative (scalar_absolute_value_norm R) setT f i) x v ->
      g x=v.
  move=> i; exact: (@measurable_approximate_partial_representative R n.+1 i setT f hfA).
have [g hg] := choice hchoose.
pose A i := partial_function_domain
  (approximate_partial_derivative (scalar_absolute_value_norm R) setT f i).
pose ep (j : nat) : R := (j.+1%:R)^-1.
have hep j : 0<ep j by rewrite /ep invr_gt0 ltr0n.
pose B (i : 'I_n.+1) j p :=
  approximate_partial_uniform_cutoff i f (g i) (ep j) (ep j) p.
pose C (i : 'I_n.+1) j p q :=
  coordinate_measurable_slice_cutoff i f (g i) (ep j) (ep j) p q.
have hBm i j p : measure_measurable mu (B i j p).
  exact: (@approximate_partial_uniform_cutoff_measurable R n.+1 i f (g i)
    (ep j) (ep j) p hf (hg i).1).
have hBi i j p q : (p<=q)%N -> B i j p `<=` B i j q.
  exact: (@approximate_partial_uniform_cutoff_increasing R n.+1 i f (g i)
    (ep j) (ep j) p q).
have hBe i j : (\bigcup_p B i j p)=A i.
  exact: (@approximate_partial_uniform_cutoffs_exhaust R n.+1 i f (g i)
    (ep j) (ep j) (hep j) (hep j) (hg i).2).
have hCm i j p q : measure_measurable mu (C i j p q).
  exact: (@coordinate_measurable_slice_cutoff_measurable R n.+1 i f (g i)
    (ep j) (ep j) p q hf (hg i).1).
have hCi i j p q r : (q<=r)%N -> C i j p q `<=` C i j p r.
  exact: (@coordinate_measurable_slice_cutoff_increasing R n.+1 i f (g i)
    (ep j) (ep j) p q r).
have hCn i j p : mu (B i j p `\` \bigcup_q C i j p q)=0%E.
  exact: (@coordinate_measurable_slice_cutoffs_conull R n.+1 i f (g i)
    (ep j) (ep j) p hf (hg i).1 (hep j) (hep j)).
apply: (@countably_finite_large_subsets_almost R [the choiceType of X] mu
  (\bigcap_i A i) _ hm (euclidean_lebesgue_countably_measurable R n.+1)).
move=> E hEA hE e he.
have [p [q hpq]] := @finite_family_two_stage_cutoffs R [the choiceType of X]
  [the finType of 'I_n.+1] mu A E B C hm hEA hE hBm hBi hBe hCm hCi hCn e he.
pose H : set X := \bigcap_j \bigcap_i C i j (p j) (q j).
exists H; split=> // a ha.
pose L := hom_of_linear (basis_interpolation (@coordinate_basisP R n.+1)
  (fun i=>g i a)).
have hL i : L (@coordinate_basis R n.+1 i)=g i a.
  by rewrite /L hom_of_linearE basis_interpolationE.
exists L; split.
- apply: (@approximate_coordinate_mass_criterion R n f g a L
    ((2 : R)^+(n.+1+1)) hL).
  + by rewrite exprn_ge0 // ler0n.
  + move=> j.
    exists (Num.min ((p j).+1%:R)^-1 ((q j).+1%:R)^-1).
    split; first by rewrite lt_min !invr_gt0 !ltr0n.
    move=> r hr; rewrite lt_min=> /andP [hrp hrq] i.
    have hCa : C i j (p j) (q j) a := ha j Logic.I i Logic.I.
    exact: (@coordinate_measurable_slice_cutoff_mass R n.+1 i f (g i)
      (ep j) (ep j) (p j) a (q j) r (ltW (hep j)) hCa hr hrp hrq).
- move=> i.
  have hCa : C i 0 (p 0) (q 0) a := ha 0 Logic.I i Logic.I.
  have hBa := @coordinate_measurable_slice_cutoff_subset R n.+1 i f (g i)
    (ep 0) (ep 0) (p 0) (q 0) a hCa.
  have [v hv] := hBa.1.
  by rewrite hL ((hg i).2 a v hv).
Qed.
