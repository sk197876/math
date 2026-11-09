(** Federer (1969), 3.3.4, pp. 290–291:
    prove existence of the actual direction map
    from the earlier normalization and Borel range
    reduction laws. All auxiliary witnesses stay
    local to this existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric InnerNorm InnerUnitNormalization ConstrainedUnitSphere SymmetricSquareGeometry
  UnitSphereSpace MetricSubsetBackground StructureProjectiveSpace
  StructureProjectiveActionTopology StructureDirectionMapUP
  ClosedSubsetBorelRetractionUP ClosedSubsetBorelRetractionSealed
  BorelFunctionUP BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projective_direction_map_exists]:
    the map f used in Federer 3.3.4,
    pp. 290–291, exists as a Borel map
    into the original projective sphere. Its
    formula on the nonzero projection domain
    is exact. Only a local auxiliary sphere
    point and the sealed Borel retraction
    support the irrelevant values off that domain. *)
Theorem structure_projective_direction_map_exists (R:realType) (X:metricType R)
    m (q:X->inner_metric_space (@euclidean_inner_productP R m.+1)):
  is_borel_function q ->
  exists f:X->structure_projective_space R m,is_structure_projective_direction_map q f.
Proof.
move=>hQ.
pose E:=inner_metric_space (@euclidean_inner_productP R m.+1).
pose S:=@euclidean_unit_sphere_set R m.+1.
pose s0:metric_subset S:=@euclidean_unit_sphere_point R m.+1 (ltn0Sn m).
have hS:closed S:=@inner_unit_sphere_closed R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1).
pose r:=@ClosedSubsetBorelRetraction.value R E S s0 hS.
have [hR hFix]:=@ClosedSubsetBorelRetraction.laws R E S s0 hS.
pose u:E->E:=inner_unit_normalization (@euclidean_inner_productP R m.+1).
pose f:=(@structure_projective_quotient R m) \o r \o u \o q.
exists f; split.
- have hU:is_borel_function u:=@inner_unit_normalization_borel R (R_n R m.+1)
    (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1).
  have hQuot:=continuous_borel_function (@structure_projective_quotient_continuous R m).
  have hQR:=@borel_function_composition E (metric_subset S)
    (structure_projective_space R m) r (@structure_projective_quotient R m) hR hQuot.
  have hQRU:=@borel_function_composition E E (structure_projective_space R m)
    u ((@structure_projective_quotient R m) \o r) hU hQR.
  exact:(@borel_function_composition X E (structure_projective_space R m)
    q (((@structure_projective_quotient R m) \o r) \o u) hQ hQRU).
- move=>x hx.
  change (inner_projective_square (val (r (u (q x))))=
    inner_projective_square (u (q x))).
  rewrite hFix=>//.
  exact:inner_unit_normalization_norm hx.
Qed.
