(** Federer (1969), 3.4.5, p. 321, citing Cartan
    (1957), pp. 97–99: the adapted cubic surface is
    actually locally analytic throughout the whole ambient R^3.
    Its global analytic rigidity is a separate assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness NormMetric
  CartanSurfaceUP CartanSurfaceSealed CartanSurfaceGeometry CartanSurfaceClosed
  FiniteAnalyticVarietyUP AnalyticVarietyGermUP ClosedSetLocalAnalytic
  CartanSurfaceOffEndpoint CartanSurfaceEndpointVariety.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cartan_surface_locally_analytic]: the actual
    local-analytic-set assertion in the example cited at
    3.4.5, p. 321. The original flat-plane and
    off-plane neighbourhoods and the complement are all proved. *)
Theorem cartan_surface_locally_analytic (R:realType):
  is_analytic_set_in (inner_norm_real_norm (@euclidean_inner_productP R 3))
    setT (@CartanSurface.set R).
Proof.
apply:(closed_set_local_analytic_suffices (@cartan_surface_closed R))=>a ha.
case:(eqVneq (a ord_max) 1)=>[hEndpoint|hAway].
- exact:(@cartan_surface_endpoint_variety R a ha hEndpoint).
- exists [set v:R_n R 3|v ord_max!=1];split;first exact:hAway.
  exact:(@cartan_surface_off_endpoint_variety R).
Qed.

(** Source for [cartan_surface_closed_proper_locally_analytic]:
    the actual closed, proper and locally analytic source
    needed for the local/global distinction cited in 3.4.5,
    p. 321. These properties carry no rigidity hypothesis. *)
Theorem cartan_surface_closed_proper_locally_analytic (R:realType):
  @closed (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 3)))
    (@CartanSurface.set R) /\
  (exists v:R_n R 3,~CartanSurface.set v) /\
  is_analytic_set_in (inner_norm_real_norm (@euclidean_inner_productP R 3))
    setT (@CartanSurface.set R).
Proof.
split;first exact:cartan_surface_closed.
split;[exact:cartan_surface_is_proper|exact:cartan_surface_locally_analytic].
Qed.
