(** The actual slice measure in Federer (1969), 2.10.16, p. 178: integrate
    I_1^{j+m-n}(A intersect Z) over the space of j-dimensional affine
    subspaces. The slice measure is the already defined ambient integral-
    geometric measure, as printed. The working Federer erratum has no
    correction to p. 178. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric Hom
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures EuclideanLebesgueDimensions
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces IsotropyGroupTopology LinearGroupTopology
  LinearGroupSealed CompactGroupHaarNormalisation OrthogonalProbabilityBackground AffineSubspaceSpace
  OrthogonalProjectionFibres AffineSubspaceParametrisation IntegralGeometricMeasure ProjectionBeta
  ProjectionNormalJacobian LinearOrbitMultiplicityIntegral ExtendedRealOrderTopology PartialFunctionBasic
  TopologicalBorel BorelFamilyBasic MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralGraphEquivalence
  ProductMeasure MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [affine_integral_geometric_slice]: direct
    inner value I_1^r(A intersect Z), r=j+m-n, in
    the middle formula of 2.10.16, p. 178. It
    uses the actual affine point set and the existing
    ambient measure; it is not an assumed slice functional. *)
Definition affine_integral_geometric_slice (R : realType) (n d r : nat) (hrn : (r<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (Z : affine_subspace_carrier (R_n R n) d) : extended_real_line R :=
  @integral_geometric_measure R n r hrn 1 (A `&` affine_points Z).

(** Source for [affine_integral_geometric_slice_nonnegative]:
    supporting nonnegative slice integrand for 2.10.16,
    p. 178, from the established measure laws. *)
Lemma affine_integral_geometric_slice_nonnegative (R : realType) (n d r : nat) (hrn : (r<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) Z :
  0<=@affine_integral_geometric_slice R n d r hrn A Z.
Proof. exact (@measure_nonnegative R [the choiceType of inner_metric_space (@euclidean_inner_productP R n)] _
  (@integral_geometric_measure_is_measure R n r hrn 1 (lexx _)) (A `&` affine_points Z)). Qed.

(** Source for [affine_integral_geometric_slice_fibre]:
    supporting fibre description of the actual slice
    value in 2.10.16, p. 178, by the point-set
    equation of 2.7.16(7), p. 140. *)
Lemma affine_integral_geometric_slice_fibre (R : realType) (n d r : nat)
    (hdn : (d<=n)%N) (hrn : (r<=n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n (n-d)) y :
  affine_integral_geometric_slice hrn A (projection_fibre hdn p y)=
    @integral_geometric_measure R n r hrn 1 (A `&` [set x | euclidean_projection_linear p x=y]).
Proof.
rewrite /affine_integral_geometric_slice; congr (integral_geometric_measure _ _).
apply/seteqP; split=> x [hx hy]; split=> //.
- exact: (@projection_fibreE R n d hdn p y x).1 hy.
- exact: (@projection_fibreE R n d hdn p y x).2 hy.
Qed.

(** Source for [euclidean_projection_slice_borel]: supporting
    Borel slice for 2.10.16, p. 178. A continuous
    projection has closed point fibres, so intersection
    with the given Borel set remains Borel. *)
Lemma euclidean_projection_slice_borel (R : realType) (n a : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n a) y :
  borel_set A -> borel_set (A `&` [set x | euclidean_projection_linear p x=y]).
Proof.
move=> hA; apply: (borel_family_binary_intersection (borel_sets_family _) hA).
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R a)].
have hc : closed ([set y] : set Y).
  apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
apply: closed_borel_set.
exact ((proj1 (continuous_closedP (euclidean_projection_linear p : X -> Y)))
  (@euclidean_projection_continuous R n a p) [set y] hc).
Qed.

Section OrbitCount.
Variable R : realType.
Variables n r : nat.
Hypothesis hrn : (r<=n)%N.
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation X := [the metricType R of inner_metric_space hBn].
Local Notation Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R r)].
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.
Local Notation ht := (@orthogonal_probability_is_measure R n mulO theta htheta).
Local Notation Ar := (orthogonal_projection_action (@euclidean_inner_productP R r) hBn hbn hO).

(** Source for [projection_haar_joint_multiplicity_integral]:
    supporting actual offset/Haar-frame integral of each
    slice in 2.10.16, p. 178. The rotational count
    formula for a projection has unit normal Jacobian,
    giving exactly beta_1(n,r) I_1^r of the slice. *)
Lemma projection_haar_joint_multiplicity_integral
    (q : orthogonal_projection_metric_space R n r) (A : set X) :
  (0<r)%N -> borel_set A ->
  is_measure_integral (product_measure (@euclidean_lebesgue_is_measure R r) ht)
    (partial_function_total (fun z : Y*O =>
      (@mapping_multiplicity R X Y (euclidean_projection_linear (Ar z.2 q)) A z.1 : extended_real_line R)))
    ((@projection_beta R n r hrn 1)%:E*@integral_geometric_measure R n r hrn 1 A).
Proof.
move=> hrpos hA.
have hi := @linear_orthogonal_average_multiplicity_integral R n r hrn mulO invO eO hO
  theta htheta (euclidean_projection_linear q) A hrpos hA.
rewrite euclidean_projection_normal_jacobian_unit mul1e in hi.
apply: (@measure_integral_graph_equivalent R (Y*O)%type
  (product_measure (@euclidean_lebesgue_is_measure R r) ht) _ _ _ _ hi)=> -[y g] z.
have he : (fun x : X => euclidean_projection_linear q (orthogonal_element_map (invO g) x))=
    euclidean_projection_linear (Ar g q).
  apply/funext=> x; exact: esym (orthogonal_projection_actionE hO g q x).
change (@mapping_multiplicity R X Y (fun x => euclidean_projection_linear q (orthogonal_element_map (invO g) x)) A y=z <->
  @mapping_multiplicity R X Y (euclidean_projection_linear (Ar g q)) A y=z).
by rewrite he.
Qed.
End OrbitCount.
