(** Federer (1969), 3.2.6, p. 245: the source
    and target integrands for an arbitrary real weight.
    The original source derivative remains partial inside A;
    the multiplicity includes infinite fibres with 0 times
    infinity interpreted by the book's convention. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  EuclideanCurveSpeedMeasure EuclideanCurveRestrictedSpeed EuclideanCurveMultiplicityMeasure MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_area_source_integrand]: the integrand
    (g composed with f)|f'| on A in the first equation
    of Federer 3.2.6, p. 245, using exact partial
    speed and the subset integral's opaque zero extension. *)
Definition curve_area_source_integrand (R:realType) n (f:R->R_n R n)
    (A:set (real_line_metric R)) (g:R_n R n->R):=
  partial_function_zero_extension (0:extended_real_line R) A
    (partial_density_product (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R))
      (euclidean_curve_speed f)).

(** Source for [curve_area_target_integrand]: the actual
    multiplicity product g(y)N(f|A,y) in the first
    equation of Federer 3.2.6, p. 245. *)
Definition curve_area_target_integrand (R:realType) n (f:R->R_n R n)
    (A:set (real_line_metric R)) (g:R_n R n->R):=
  partial_function_total (fun y=>((g y)%:E*
    @mapping_multiplicity R [the choiceType of real_line_metric R] (R_n R n) f A y:extended_real_line R)).

(** Source for [curve_area_restricted_speed_product_graph]:
    supporting relocation of the subset cutoff in Federer
    3.2.6, p. 245. The two integrands have exactly
    the same graph, including undefined derivatives in A. *)
Lemma curve_area_restricted_speed_product_graph (R:realType) n (f:R->R_n R n)
    (A:set (real_line_metric R)) (g:R_n R n->R) x z:
  partial_function_graph (curve_area_source_integrand f A g) x z <->
  partial_function_graph (partial_density_product
    (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R))
    (euclidean_curve_restricted_speed f A)) x z.
Proof.
case:(pselect (A x))=>hx.
- rewrite /curve_area_source_integrand (partial_function_zero_extension_on _ _ _ hx).
  split=>h.
  + have [r [s [hr [hs he]]]]:=(partial_density_product_graph _ _ x z).1 h.
    apply/partial_density_product_graph; exists r,s; split=>//; split=>//.
    apply/partial_function_zero_extension_graph; left; by split.
  + have [r [s [hr [hs he]]]]:=(partial_density_product_graph _ _ x z).1 h.
    apply/partial_density_product_graph; exists r,s; split=>//; split=>//.
    exact ((partial_function_zero_extension_on _ _ _ hx).1 hs).
- rewrite /curve_area_source_integrand (partial_function_zero_extension_off _ _ _ hx).
  split=>h.
  + subst z; apply/partial_density_product_graph; exists (g (f x))%:E,0.
    split=>//; split; last exact:mule0.
    apply/partial_function_zero_extension_graph; right; by split.
  + have [r [s [hr [hs he]]]]:=(partial_density_product_graph _ _ x z).1 h.
    have hs0:=(partial_function_zero_extension_off _ _ _ hx).1 hs.
    by rewrite -he hs0 mule0.
Qed.

(** Source for [curve_area_multiplicity_product_graph]: the
    target weight and actual multiplicity form the pointwise
    density product in Federer 3.2.6, p. 245. *)
Lemma curve_area_multiplicity_product_graph (R:realType) n (f:R->R_n R n)
    (A:set (real_line_metric R)) (g:R_n R n->R) y z:
  partial_function_graph (partial_density_product
    (partial_function_total (fun y=>(g y)%:E:extended_real_line R))
    (euclidean_curve_multiplicity_density f A)) y z <->
  partial_function_graph (curve_area_target_integrand f A g) y z.
Proof.
split.
- move=>h; have [r [s [hr [hs he]]]]:=(partial_density_product_graph _ _ y z).1 h.
  change ((g y)%:E=r) in hr.
  change (@mapping_multiplicity R [the choiceType of real_line_metric R] (R_n R n) f A y=s) in hs.
  change ((g y)%:E*@mapping_multiplicity R [the choiceType of real_line_metric R] (R_n R n) f A y=z).
  by rewrite hr hs.
- move=>hz; apply/partial_density_product_graph.
  exists (g y)%:E,(@mapping_multiplicity R [the choiceType of real_line_metric R] (R_n R n) f A y).
  by split=>//; split.
Qed.
