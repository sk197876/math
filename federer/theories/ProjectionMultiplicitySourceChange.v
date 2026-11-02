(** Supporting the source rotations in Federer (1969), 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Parts 6–7, pp. 247–250. Fibre bijections
    identify projection multiplicity integrals after a change of source
    coordinates. No measurability or finite-fibre hypothesis is needed for
    this pointwise identity of the lower integrals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric Hom
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures
  OrthogonalInjectionSpaces OrthogonalGroupHaarMeasure OrthogonalGroupTopology IsotropyGroupTopology
  LinearGroupSealed ProjectionMultiplicityIntegral MappingMultiplicity BijectionPrecompositionMultiplicity
  PartialFunctionBasic MeasureIntegralBounds TopologicalBorel ContinuousBorelPreimages
  EuclideanOrthogonalBlockExtension TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_multiplicity_integral_source_change]:
    supporting fibre-bijection identity for 2.10.46, p. 204;
    Freilich (1950), Part 6, pp. 247–249.
    An explicit inverse and the composition law suffice even
    for nonmeasurable source sets and infinite multiplicities. *)
Lemma projection_multiplicity_integral_source_change (R : realType) n m
    (p q : orthogonal_projection_metric_space R n m)
    (u v : R_n R n -> R_n R n)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  cancel u v -> cancel v u ->
  (forall x, euclidean_projection_linear q x=euclidean_projection_linear p (u x)) ->
  projection_multiplicity_integral A q=projection_multiplicity_integral (u @` A) p.
Proof.
move=> huv hvu hq.
have hf : (euclidean_projection_linear q : R_n R n -> R_n R m)=
    (fun x=>euclidean_projection_linear p (u x)).
  exact: funext hq.
have he : (fun y=>@mapping_multiplicity R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    (euclidean_projection_linear q) A y)=
    (fun y=>@mapping_multiplicity R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    (euclidean_projection_linear p) (u @` A) y).
  apply: funext=> y; rewrite hf.
  exact: bijective_precomposition_multiplicity huv hvu.
by rewrite /projection_multiplicity_integral /projection_multiplicity_integrand he.
Qed.

Section OrthogonalSourceChange.
Variable R : realType.
Variable n : nat.
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation X := (inner_metric_space (@euclidean_inner_productP R n)).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n)) O mulO invO eO.

(** Source for [orthogonal_source_image_borel]: supporting Borel
    source rotations for the cylinder formula of 2.10.46,
    p. 204; Freilich (1950), Part 6, pp. 247–249.
    The image is the continuous inverse map's preimage. *)
Lemma orthogonal_source_image_borel (g : O) (A : set X) :
  borel_set A -> @borel_set X (orthogonal_element_map g @` A).
Proof.
move=> hA.
have [hgi hig] := orthogonal_element_inv hO g.
have he : orthogonal_element_map g @` A=orthogonal_element_map (invO g) @^-1` A.
  apply/seteqP; split=> y.
  - by move=> [x hx <-]; rewrite /= hgi.
  - move=> hy; exists (orthogonal_element_map (invO g) y)=> //; exact hig.
have hc : continuous (fun x : X=>(orthogonal_element_map (invO g) x : X)).
  have hp : continuous (fun x : X=>((invO g,x) : O*X)).
    apply: topological_pair_continuous; first exact: cst_continuous.
    by move=> x; exact: cvg_id.
  move=> x; exact (continuous_comp (hp x)
    (@euclidean_orthogonal_evaluation_continuous R n (invO g,x))).
rewrite he; exact (@continuous_borel_preimage X X _ hc A hA).
Qed.

(** Source for [projection_multiplicity_integral_orthogonal_action]:
    supporting rotation identity for 2.10.46, p. 204;
    Freilich (1950), Part 6, pp. 247–249.
    The action on projections uses the inverse source rotation. *)
Lemma projection_multiplicity_integral_orthogonal_action m (g : O)
    (p : orthogonal_projection_metric_space R n m) (A : set X) :
  projection_multiplicity_integral A
    (orthogonal_projection_action (@euclidean_inner_productP R m)
      (@euclidean_inner_productP R n) (@coordinate_basisP R n) hO g p)=
    projection_multiplicity_integral (orthogonal_element_map (invO g) @` A) p.
Proof.
have [hgi hig] := orthogonal_element_inv hO g.
apply: (@projection_multiplicity_integral_source_change R n m p _
  (orthogonal_element_map (invO g)) (orthogonal_element_map g) A hig hgi).
move=> x; exact: orthogonal_projection_actionE.
Qed.
End OrthogonalSourceChange.
