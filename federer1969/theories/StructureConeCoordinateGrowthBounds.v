(** Federer (1969), 3.3.4, p. 289: literal radius-supremum
    bounds for the original cone and its finite coordinate cover. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerMetric StructureCone StructureCoordinateCones
  StructureCoordinateGrowth StructureRadialCostLimits StructurePlaneGrowth
  StructureCoordinateGrowthLaws StructureApertureWeightScaling
  MeasureUP MeasureBasic MeasureFiniteUnionBound ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Bounds.
Variable R:realType.
Variables m k l:nat.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R (m+k))).
Variables (phi:set E->\bar R) (A:set E) (a:E).
Variable V:G (R_n R (m+k)) l.
Variable f:{linear R_n R (m+k)->R_n R (m+k)}.
Hypothesis hPhi:is_measure phi.

(** Source for [structure_plane_coordinate_lower_growth]: the lower
    cone inclusion in Federer 3.3.4, p. 289 implies the same bound for
    the exact weighted radius suprema. All positive real radii and
    extended values remain; no measurability of A is needed. *)
Theorem structure_plane_coordinate_lower_growth (j:'I_k) (delta s:R):
  0<s ->
  (forall r:R,0<r<delta ->structure_coordinate_cone A a f j r%:E s `<=`
    A `&` structure_cone V a r%:E s) ->
  (structure_coordinate_radial_supremum phi A a f j delta s<=
    structure_plane_radial_supremum m phi A a V delta s)%E.
Proof.
move=>hs hInclude; apply:extended_real_sup_least=>v [r [hr ->]].
have hMass:=measure_mono hPhi (hInclude r hr).
have hR:((0:R)%:E<=((r^-1)^+m)%:E)%E by rewrite lee_fin exprn_ge0 // invr_ge0 ltW //; exact:(andP hr).1.
have hS:((0:R)%:E<=((s^-1)^+m)%:E)%E by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
have hCost:(structure_coordinate_cost phi A a f j r s<=
    phi (A `&` structure_cone V a r%:E s)*((r^-1)^+m)%:E*((s^-1)^+m)%:E)%E.
  exact:(@lee_wpmul2r R _ hS _ _ (@lee_wpmul2r R _ hR _ _ hMass)).
apply:le_trans hCost _; apply:extended_real_sup_upper; by exists r.
Qed.

(** Source for [structure_plane_coordinate_upper_growth]: the finite
    upper cone inclusion and bounded aperture ratio of Federer 3.3.4,
    p. 289 give an exact bound by c^m times the finite sum of coordinate
    radius suprema at aperture c*s. Finite subadditivity is applied to
    original sets, and every scaling factor is positive finite. *)
Theorem structure_plane_coordinate_upper_growth (delta s c:R):
  0<s ->0<c ->
  (forall r:R,0<r<delta ->A `&` structure_cone V a r%:E s `<=`
    (\bigcup_j structure_coordinate_cone A a f j r%:E (c*s))) ->
  (structure_plane_radial_supremum m phi A a V delta s<=
    (c^+m)%:E*\sum_j structure_coordinate_radial_supremum phi A a f j delta (c*s))%E.
Proof.
move=>hs hc hInclude; apply:extended_real_sup_least=>v [r [hr ->]].
pose S j:=structure_coordinate_cone A a f j r%:E (c*s).
have hMass:(phi (A `&` structure_cone V a r%:E s)<=\sum_j phi (S j))%E.
  exact:le_trans (measure_mono hPhi (hInclude r hr)) (@measure_finite_union_bound R E [the finType of 'I_k] phi S hPhi).
have hR:((0:R)%:E<=((r^-1)^+m)%:E)%E by rewrite lee_fin exprn_ge0 // invr_ge0 ltW //; exact:(andP hr).1.
have hS:((0:R)%:E<=((s^-1)^+m)%:E)%E by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
have hCS:0<c*s by rewrite mulr_gt0.
have hRaw:=@lee_wpmul2r R _ hS _ _ (@lee_wpmul2r R _ hR _ _ hMass).
have hSumScale:((\sum_j phi (S j))*((r^-1)^+m)%:E*((s^-1)^+m)%:E=
    (c^+m)%:E*\sum_j structure_coordinate_cost phi A a f j r (c*s))%E.
  rewrite ge0_sume_distrl; last by move=>j _; exact:measure_nonnegative hPhi (S j).
  rewrite ge0_sume_distrl; last by move=>j _; exact:mule_ge0 (measure_nonnegative hPhi (S j)) hR.
  rewrite ge0_sume_distrr; last by move=>j _; exact:(@structure_coordinate_cost_nonnegative R m k phi A a f j r (c*s) hPhi (andP hr).1 hCS).
  apply:eq_bigr=>j _; exact:structure_aperture_weight_scaling hc.
rewrite hSumScale in hRaw; apply:le_trans hRaw _.
apply:lee_wpmul2l; first by rewrite lee_fin exprn_ge0 // ltW.
apply:lee_sum=>j _; apply:extended_real_sup_upper; by exists r.
Qed.
End Bounds.
