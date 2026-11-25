(** Mean angular Jacobian of two independent normal frames, supporting
    Federer (1969), 2.10.16, p. 178. Integrate the unit-vector wedge formula
    of 2.7.16(6), p. 139, first in the second frame, then in the first.
    Joint continuity is proved through the relative rotation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanProjectionMetric EuclideanOrthogonalInvariantMeasures OrthogonalGroupTopology
  OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces IsotropyGroupTopology LinearGroupTopology
  LinearGroupSealed CompactGroupHaarNormalisation OrthogonalProbabilityBackground
  AffineSubspaceInvariantMeasure StackedNormalFamily EuclideanNormalJacobian StackedNormalOrbitJacobian
  StackedNormalJacobianAverage ProjectionBeta CountableBorelProduct ProductMeasure
  ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasurableFunctionUP MeasurableGraphEquivalence
  ContinuousRealIntegrandMeasurable SummableRealFunctionUP TotalNonnegativeProductIntegral
  PositiveCharacteristicMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section PairIntegral.
Variable R : realType.
Variables n a r : nat.
Hypotheses (hamn : (a+r<=n)%N) (hrna : (r<=n-a)%N).
Local Notation hnr := (leq_trans (leq_addl a r) hamn).
Local Notation O := (euclidean_orthogonal_group R n).
Local Notation P := (orthogonal_projection_metric_space R n a).
Local Notation Q := (orthogonal_projection_metric_space R n r).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Variables (mulO : O -> O -> O) (invO : O -> O) (eO : O).
Hypothesis hO : is_subgroup_restriction (linear_group_mul hBn hbn)
  (linear_group_inv hBn hbn) (linear_group_unit hBn hbn) O mulO invO eO.
Variable theta : set O -> \bar R.
Hypothesis htheta : is_normalised_haar_measure mulO theta.
Variable F : P*Q -> {linear R_n R n -> R_n R (a+r)}.
Hypothesis hF : is_stacked_normal_family F.
Local Notation ht := (@orthogonal_probability_is_measure R n mulO theta htheta).
Local Notation Aa := (orthogonal_projection_action (@euclidean_inner_productP R a) hBn hbn hO).
Local Notation Ar := (orthogonal_projection_action (@euclidean_inner_productP R r) hBn hbn hO).

(** Source for [stacked_normal_pair_integral]: supporting
    actual product Haar integral of the angular factor
    in 2.10.16, p. 178. Its value is the same
    beta ratio as the single-frame wedge average; no
    generic-position hypothesis is added. *)
Theorem stacked_normal_pair_integral (p : P) (q : Q) :
  is_measure_integral (product_measure ht ht)
    (partial_function_total (fun z : O*O =>
      (euclidean_normal_jacobian (F (Aa z.1 p,Ar z.2 q)))%:E))
    ((@projection_beta R n r hnr 1 / @projection_beta R (n-a) r hrna 1)%R)%:E.
Proof.
pose mu := product_measure ht ht.
pose hm := product_measure_is_measure ht ht.
have hr := @orthogonal_probability_borel_regular R n mulO invO eO hO theta htheta.
have hw := @orthogonal_probability_whole_countably_measurable R n mulO theta htheta.
have hbase := @orthogonal_group_countable_base R n.
have [_ [hreg hwhole]] := @countable_borel_product_background R O O theta theta ht ht hbase hbase hr hr hw hw.
pose f (z : O*O) : extended_real_line R := (euclidean_normal_jacobian (F (Aa z.1 p,Ar z.2 q)))%:E.
have hpos z : 0<=f z by rewrite /f lee_fin; exact: euclidean_normal_jacobian_nonnegative.
have hfc := @stacked_normal_jacobian_pair_continuous R n a r mulO invO eO hO F hF p q.
have hfm := @continuous_real_integrand_measurable R (O*O)%type mu
  (fun z => euclidean_normal_jacobian (F (Aa z.1 p,Ar z.2 q))) hm hreg hfc.
have hf : is_measure_measurable_function mu (partial_function_total f).
  apply: (@measurable_function_graph_equivalent R (O*O)%type (extended_real_line R) mu _ _ _ hfm)=> z y.
  rewrite real_total_integrand_graph; by [].
pose c := (@projection_beta R n r hnr 1 / @projection_beta R (n-a) r hrna 1)%R.
have hc : (0<=c)%R by apply: divr_ge0; exact: ltW (projection_beta_positive _ (lexx _)).
have hsec s : is_measure_integral theta (partial_function_total (fun t => f (s,t))) c%:E.
  exact (@stacked_normal_jacobian_haar_average R n a r hamn hrna mulO invO eO hO theta htheta F hF (Aa s p) q).
have hout := @total_nonnegative_product_vertical_sections R O O theta theta ht ht f (fun _ => c%:E)
  hwhole hpos hf hsec.
have hcE : 0<=c%:E by rewrite lee_fin.
have hconst := @nonnegative_extended_constant_integral R O theta ht c%:E hcE.
rewrite htheta.2 mule1 in hconst.
have he := measure_integral_unique hout hconst.
have hi := total_nonnegative_integral_specification hm hpos hf.
by rewrite he in hi.
Qed.
End PairIntegral.
