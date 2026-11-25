(** Federer (1969), 4.1.20, p. 378, first proof sentence:
    the null-projection characterization of 2.10.5, p. 173,
    and orthogonal invariance give one rotation for which
    every member of a prescribed finite family of orthogonal
    projections has null image. The original set is arbitrary;
    its required Borel hull is produced by 2.10.5. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric EuclideanProjectionMetric EuclideanProjectionSpace
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed HomogeneousSpaceUP
  EuclideanOrthogonalInvariantMeasures CompactGroupHaarNormalisation
  CompactGroupHomogeneousMeasures OrthogonalProjectionProbability
  IntegralGeometricMeasure IntegralGeometricNullSets ProjectedVolumeMeasurability
  OrthogonalProbabilityBackground ProjectionCompositionProbability
  HaarIntegralUP MeasurePushforward MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureAlmostPositiveWitness EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [integral_geometric_finite_null_projections]: the
    simultaneous good-rotation choice in Federer 4.1.20,
    p. 378. This is the finite-family form of the printed
    Lambda(n,m) choice. No measurability, finite measure or
    rectifiability hypothesis is imposed on the original set. *)
Theorem integral_geometric_finite_null_projections
    (R:realType) n m (hmn:(m<=n)%N) (I:finType)
    (p:I->orthogonal_projection_metric_space R n m)
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  @integral_geometric_measure R n m hmn 1 A=0->
  exists g:euclidean_orthogonal_group R n,forall i:I,
    @euclidean_lebesgue_measure R m
      ((fun x=>euclidean_projection_linear (p i) (orthogonal_element_map g x)) @` A)=0.
Proof.
move=>hNull.
have[B [hAB [hB hAlmost]]]:=
  @integral_geometric_one_null_projection_hull R n m hmn A hNull.
have[mulS [invS [eS hS]]]:=@orthogonal_group_restriction_exists R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
have[theta hTheta]:=@orthogonal_normalised_haar_measure_exists R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n) mulS invS eS hS.
pose O:=[the topologicalType of set_type (euclidean_orthogonal_group R n)].
pose AP:=orthogonal_projection_action (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hS.
have hPush i:measure_pushforward (orbit_map AP (p i)) theta=
    @orthogonal_projection_probability R n m hmn.
  exact:(@projection_probability_orbit R n m hmn mulS invS eS hS theta (p i) hTheta).
have hMeasure:=@orthogonal_probability_is_measure R n mulS theta hTheta.
pose P:=fun i:I=>[set g:O|projected_volume_function B (AP g (p i))=0].
have hEach i:measure_almost_everywhere theta (P i).
  have h:=hAlmost.
  rewrite -(hPush i) /measure_almost_everywhere /measure_pushforward in h.
  exact:h.
pose D:set I:=setT.
have hAll:=@measure_almost_everywhere_countable R O I theta hMeasure D P
  (finite_set_countable (@finite_finset I setT)) (fun i _=>hEach i).
have hNonzero:theta setT<>0.
  rewrite hTheta.2;move=>hEqual.
  have hOne:(1:R)=0:=EFin_inj hEqual.
  have hDifferent:(1:R)!=0 by rewrite oner_eq0.
  apply:(negP hDifferent);apply/eqP;exact:hOne.
have[g [_ hGood]]:=@measure_almost_positive_set_witness R O theta hMeasure
  setT (\bigcap_(i in D) P i) hNonzero hAll.
exists (invS g)=>i.
have hProjected:=hGood i Logic.I.
change (@euclidean_lebesgue_measure R m
  (euclidean_projection_linear (AP g (p i)) @` B)=0) in hProjected.
apply:(@measure_null_subset R (R_n R m) (@euclidean_lebesgue_measure R m)
  (@euclidean_lebesgue_is_measure R m) _ _ _ hProjected).
move=>y [x hx <-].
exists x;first exact:hAB x hx.
exact:esym (orthogonal_projection_actionE hS g (p i) x).
Qed.
