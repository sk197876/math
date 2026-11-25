(** Federer (1969), 2.10.16, p. 178, middle displayed formula: I_1^m(A)
    equals beta_1(j,j+m-n)/beta_1(n,m) times the gamma_{n,j} integral of
    I_1^{j+m-n}(A intersect Z). Reindex m=n-j+r, r>0, to keep all Euclidean
    dimensions natural without coercing slice carriers. The statement uses
    the actual gamma of 2.7.16(7), p. 141, and the actual ambient I_1^r. The
    proof is double counting through stacked normal maps, polar
    factorisation and the unit-wedge average, not an assumed
    integral-geometric transformation law. No p. 178 entry occurs in the
    working Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures EuclideanLebesgueDimensions
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces OrthogonalEuclidean
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed CompactGroupHaarNormalisation OrthogonalProbabilityBackground
  AdjointUP Adjoint AffineSubspaceSpace AffineSubspaceParametrisation AffineSubspaceInvariantMeasure
  AffineGeometricSlice AffineParameterGeometricIntegral ProjectionBeta IntegralGeometricMeasure
  ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence ProductMeasureUP ProductMeasure MeasureBijectionLaws
  MeasureBijectionCoordinateTransport MeasureBijectionTotalIntegral PushforwardIntegral PushforwardTotalNonnegativeIntegral TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [affine_geometric_slice_dimension_bound]:
    supporting dimension arithmetic for the middle formula
    of 2.10.16, p. 178: r<=d<=n implies n-d+r<=n. *)
Lemma affine_geometric_slice_dimension_bound (n d r : nat) :
  (d<=n)%N -> (r<=d)%N -> (n-d+r<=n)%N.
Proof.
move=> hdn hrd; have h := leq_add (leqnn (n-d)) hrd.
by rewrite subnK in h.
Qed.

(** Source for [affine_geometric_slice_codimension_bound]:
    supporting dimension arithmetic for 2.10.16,
    p. 178: the complement of the codimension n-d
    has dimension d, so r<=d supplies the angular beta. *)
Lemma affine_geometric_slice_codimension_bound (n d r : nat) :
  (d<=n)%N -> (r<=d)%N -> (r<=n-(n-d))%N.
Proof. by move=> hdn hrd; rewrite subKn. Qed.

Section AffineSlicing.
Variable R : realType.
Variables n d r : nat.
Hypotheses (hdn : (d<=n)%N) (hrd : (r<=d)%N).
Local Notation a := (n-d)%N.
Local Notation hmn := (affine_geometric_slice_dimension_bound hdn hrd).
Local Notation hrna := (affine_geometric_slice_codimension_bound hdn hrd).
Local Notation hrn := (leq_trans hrd hdn).
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation Ea := [the metricType R of inner_metric_space (@euclidean_inner_productP R a)].
Local Notation X := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.
Variable p : orthogonal_projection_metric_space R n a.
Local Notation xi := (affine_parametrisation hdn p).
Local Notation gamma := (@affine_invariant_measure R n d hdn mulO p theta htheta).
Local Notation ht := (@orthogonal_probability_is_measure R n mulO theta htheta).
Local Notation hLa := (@euclidean_lebesgue_is_measure R a).

(** Source for [federer_2_10_16_affine_slicing]: direct middle
    formula of 2.10.16, p. 178, with j=d,
    m=n-d+r and r=j+m-n>0. The first conclusion
    proves the actual gamma integral, including infinity;
    the second gives the printed normalized equality.
    The chosen presentation of O(n), normalized Haar
    measure and initial projection are arbitrary. *)
Theorem federer_2_10_16_affine_slicing (A : set X) :
  (0<r)%N -> borel_set A ->
  is_measure_integral gamma
    (partial_function_total (@affine_integral_geometric_slice R n d r hrn A))
    (((@projection_beta R n (a+r) hmn 1 / @projection_beta R d r hrd 1)%R)%:E*
      @integral_geometric_measure R n (a+r) hmn 1 A) /\
  @integral_geometric_measure R n (a+r) hmn 1 A=
    (((@projection_beta R d r hrd 1 / @projection_beta R n (a+r) hmn 1)%R)%:E*
      measure_lower_integral gamma (partial_function_total (@affine_integral_geometric_slice R n d r hrn A))).
Proof.
move=> hrpos hA.
have [u hu] := @euclidean_orthogonal_injection_exists R n r hrn.
pose qlin := inner_adjoint (@euclidean_inner_productP R r) hBn (@coordinate_basisP R r) u.
have hq : is_orthogonal_projection (@euclidean_inner_product R n) (@euclidean_inner_product R r) qlin.
  exists u; split=> //; exact: inner_adjointP.
pose q := orthogonal_projection_of (@euclidean_inner_productP R r) hBn hbn hq.
have hi := @affine_parameter_geometric_slice_integral R n d r hmn hrna mulO invO eO hO
  theta htheta p q A hrpos hA.
have heproof : leq_trans (leq_addl a r) hmn=hrn := Prop_irrelevance _ _.
rewrite heproof in hi.
have hedim : (n-a)%N=d := subKn hdn.
have hebeta : @projection_beta R (n-a) r hrna 1=@projection_beta R d r hrd 1.
  move: hrna; rewrite hedim=> h; by rewrite (Prop_irrelevance h hrd).
rewrite hebeta in hi.
pose v := @affine_integral_geometric_slice R n d r hrn A.
pose f (z : Ea*O) : extended_real_line R := @integral_geometric_measure R n r hrn 1
  (A `&` [set x | euclidean_projection_linear (orthogonal_projection_action
    (@euclidean_inner_productP R a) hBn hbn hO z.2 p) x=z.1]).
have hp z : 0<=f z := measure_nonnegative (@integral_geometric_measure_is_measure R n r hrn 1 (lexx _)) _.
have hswap := measure_bijection_swap ht hLa.
have hit := measure_bijection_total_nonnegative_integral (product_measure_is_measure ht hLa)
  (product_measure_is_measure hLa ht) hswap hp hi.
have hprod : product_measure ht hLa=@affine_product_measure R n d mulO theta htheta.
  apply: (product_measure_unique (product_measure_specification ht hLa)).
  exact: product_measure_specification.
rewrite hprod in hit.
have hcomp : is_measure_integral (@affine_product_measure R n d mulO theta htheta)
    (partial_function_total (fun z : O*Ea => v (xi z)))
    (((@projection_beta R n (a+r) hmn 1 / @projection_beta R d r hrd 1)%R)%:E*
      @integral_geometric_measure R n (a+r) hmn 1 A).
  apply: (@measure_integral_graph_equivalent R (O*Ea)%type
    (@affine_product_measure R n d mulO theta htheta) _ _ _ _ hit)=> -[s y] z.
  have he : v (xi (s,y))=f (y,s).
    rewrite /v (affine_parametrisation_fibre hdn hO).
    exact: affine_integral_geometric_slice_fibre.
  change (f (y,s)=z <-> v (xi (s,y))=z); by rewrite he.
have hprodM : is_measure (@affine_product_measure R n d mulO theta htheta).
  rewrite -hprod; exact: product_measure_is_measure.
have hc := (@measure_pushforward_integral_iff R (O*Ea)%type
  (affine_subspace_space (@euclidean_inner_productP R d) hBn (@coordinate_basisP R d) hbn)
  (@affine_product_measure R n d mulO theta htheta) hprodM xi (partial_function_total v)
  hcomp.1 _).1 hcomp.
split; first exact hc.
have hel := measure_lower_integral_unique (measure_lower_integral_specification gamma _) hc.2.2.
rewrite hel muleA -EFinM.
pose k := @projection_beta R n (a+r) hmn 1.
pose c := @projection_beta R d r hrd 1.
have hk : k!=0%R by rewrite gt_eqF //; exact: projection_beta_positive _ (lexx _).
have hc0 : c!=0%R by rewrite gt_eqF //; exact: projection_beta_positive _ (lexx _).
have hcoef : ((c/k)*(k/c)= 1)%R.
  by rewrite -mulrA [(k^-1*(k*c^-1))%R]mulrA (mulVf hk) mul1r (mulfV hc0).
by rewrite hcoef mul1e.
Qed.
End AffineSlicing.
