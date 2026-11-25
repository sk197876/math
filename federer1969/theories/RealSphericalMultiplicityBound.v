(** A corrected spherical bound for Federer 2.10.11, p. 176.
    The printed constant cannot be carried to arbitrary target metrics.
    The previously proved Hausdorff comparisons give the factor 2^p;
    a separate concrete example tests necessity of an additional factor. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureIntegralBounds BorelRegularMeasureUP
  TopologicalBorel CompleteMetricUP LipschitzUP LipschitzConstant NormMetricScaleContinuity
  RealPower RealHausdorffNormalisation RealHausdorffMeasure RealHausdorffMeasureLaws
  RealHausdorffLipschitz RealHausdorffMultiplicity RealPowerCoverVariants HausdorffMeasureUP
  CaratheodoryBorelRegular MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_spherical_measure_borel_regularity]: the missing
    interface connection to the Borel-regularity assertion of Federer
    2.10.1, p. 170, for the actual closed-ball construction of
    2.10.2(2), p. 171; supporting the corrected 2.10.11 bound. *)
Lemma real_spherical_measure_borel_regularity (R:realType) (X:metricType R)
    (p:R) (hp:(0<=p)%R):
  is_borel_regular_measure (@real_spherical_measure R X p hp).
Proof.
apply:(caratheodory_limit_borel_regular (@real_spherical_measure_specification R X p hp)).
- move=> j;exact:metric_real_diameter_cost_ge0 (ltW (real_hausdorff_normalisation_positive hp)).
- move=> j;apply:closed_borel_set;exact:positive_metric_closed_ball_closed (set_valP j).
Qed.

(** Source for [real_spherical_lipschitz_image_bound_corrected]: project
    correction of the spherical parenthesis in Federer 2.10.11,
    p. 176, for arbitrary metric spaces. The factor 2^p follows
    directly from H^p<=S^p<=2^p H^p and the original Hausdorff
    Lipschitz estimate; it retains every real degree p>=0. *)
Lemma real_spherical_lipschitz_image_bound_corrected (R:realType)
    (X Y:metricType R) (f:X->Y) (L p:R) (hp:(0<=p)%R):
  is_metric_lipschitz_bound setT f L -> forall A,
  @real_spherical_measure R Y p hp (f @` A)<=
    (real_power 2 p*real_power L p)%R%:E*@real_spherical_measure R X p hp A.
Proof.
move=> hf A.
have hTwo:0<=(real_power 2 p)%:E by rewrite lee_fin;exact:real_power_nonnegative.
have hL:0<=(real_power L p)%:E by rewrite lee_fin;exact:real_power_nonnegative.
apply:le_trans (@real_spherical_le_double_hausdorff R Y p hp (f @` A)) _.
apply:le_trans (lee_wpmul2l hTwo
  (@real_hausdorff_lipschitz_image_bound R X Y f L p hp hf A)) _.
rewrite muleA -EFinM.
apply:lee_wpmul2l;first by rewrite lee_fin;exact:mulr_ge0 (real_power_nonnegative _ _) (real_power_nonnegative _ _).
exact:real_hausdorff_le_spherical.
Qed.

(** Source for [federer_2_10_11_real_spherical_corrected]: a valid
    replacement for the spherical parenthesis of Federer 2.10.11,
    p. 176, with factor 2^p and every original hypothesis. Integral
    existence is a conclusion; zero degree, zero least Lipschitz
    constant and infinite source mass remain included. *)
Theorem federer_2_10_11_real_spherical_corrected (R:realType)
    (X Y:metricType R) (f:X->Y) (hlip:is_metric_lipschitz setT f)
    (p:R) (hp:(0<=p)%R) (D A:set X):
  is_complete_metric_space X -> countable D -> dense D -> borel_set A ->
  let beta:=@real_spherical_measure R Y p hp in
  let F:=partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f A y:extended_real_line R)) in
  is_measure_integral beta F (measure_lower_integral beta F) /\
    measure_lower_integral beta F<=
      (real_power 2 p*real_power (metric_lipschitz_constant hlip) p)%R%:E*
        @real_spherical_measure R X p hp A.
Proof.
move=> hX hD hden hA beta F.
pose L:=metric_lipschitz_constant hlip.
have hf:=least_metric_lipschitz_bound (metric_lipschitz_constant_specification hlip).
apply:(@continuous_borel_multiplicity_comparison R X Y f
  (@real_spherical_measure R X p hp) beta (real_power 2 p*real_power L p) D A
  hX hD hden (@real_spherical_measure_is_measure R X p hp)
  (@real_spherical_measure_borel_regularity R X p hp)
  (@real_spherical_measure_is_measure R Y p hp)
  (@real_spherical_measure_borel_regularity R Y p hp) _
  (mulr_ge0 (real_power_nonnegative _ _) (real_power_nonnegative _ _)) _ hA).
- apply:(@metric_fixed_lipschitz_continuous R X Y f L hf.1)=> x y.
  exact:hf.2 x y I I.
- move=> B _;exact:(@real_spherical_lipschitz_image_bound_corrected R X Y f L p hp hf B).
Qed.
