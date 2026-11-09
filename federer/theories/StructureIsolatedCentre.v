(** Federer (1969), 3.3.4, p. 288: if no original
    source points other than the centre occur sufficiently near
    it, alternative (1) holds for every plane. This also
    retains the elementary zero-degree endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerMetric InnerNorm StructureCone StructureConeBasic
  StructurePlaneGrowth StructurePositiveGrowthLimits StructureConeDensityValues
  MeasureUP MeasureBasic ExtendedRealBounds PositiveRadiusLimits
  PositiveRadiusLimitCongruence PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_isolated_centre_cone_empty]:
    supporting empty-cone case in Federer 3.3.4,
    p. 288. A cone excludes its vertex and lies
    inside its strict radius ball, so an isolated
    source centre contributes no source point. *)
Lemma structure_isolated_centre_cone_empty (R:realType) n k
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n))
    (V:G (R_n R n) k) (delta r s:R):
  (forall x,A x ->0<inner_norm (@euclidean_inner_productP R n) (x-a)<delta ->False) ->
  r<=delta ->A `&` structure_cone V a r%:E s=set0.
Proof.
move=>hIsolated hr; apply/seteqP; split=>x hx; last by [].
have [hA hCone]:=hx; apply:(hIsolated x hA); apply/andP; split.
- rewrite inner_norm_gt0 subr_eq0; apply/negP=>/eqP he.
  subst x; exact:(structure_cone_vertex_excluded hCone).
- have hRadius:=structure_cone_norm_bound hCone.
  rewrite lte_fin in hRadius; exact:(lt_le_trans hRadius hr).
Qed.

(** Source for [structure_isolated_centre_radial_zero]:
    the exact original radius supremum in alternative
    (1) of Federer 3.3.4, p. 288, vanishes at
    an isolated original source centre, for every aperture.
    No finiteness of the outer measure is needed. *)
Lemma structure_isolated_centre_radial_zero (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n))
    (V:G (R_n R n) k) (delta s:R):
  is_measure phi ->0<delta ->
  (forall x,A x ->0<inner_norm (@euclidean_inner_productP R n) (x-a)<delta ->False) ->
  structure_plane_radial_supremum m phi A a V delta s=0%E.
Proof.
move=>hm hDelta hIsolated.
have hEmpty r (hr:0<r<delta):A `&` structure_cone V a r%:E s=set0.
  exact:(@structure_isolated_centre_cone_empty R n k A a V delta r s hIsolated
    (ltW (andP hr).2)).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:extended_real_sup_least=>v [r [hr ->]].
  by rewrite (hEmpty r hr) (measure_empty hm) !mul0e.
- have hRadius:0<delta/2<delta:=structure_density_positive_half_bounds hDelta.
  have hVal:(0: \bar R)=
      (phi (A `&` structure_cone V a (delta/2)%:E s)*
        (((delta/2)^-1)^+m)%:E*((s^-1)^+m)%:E)%E.
    by rewrite (hEmpty _ hRadius) (measure_empty hm) !mul0e.
  apply:extended_real_sup_upper; exists (delta/2); by split.
Qed.

(** Source for [structure_isolated_centre_zero_growth]:
    alternative (1) of Federer 3.3.4, p. 288,
    holds at every plane when the original source has
    no punctured point in one positive-radius neighbourhood. *)
Theorem structure_isolated_centre_zero_growth (R:realType) n k m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n))
    (V:G (R_n R n) k) (delta:R):
  is_measure phi ->0<delta ->
  (forall x,A x ->0<inner_norm (@euclidean_inner_productP R n) (x-a)<delta ->False) ->
  structure_plane_zero_growth m phi A a V.
Proof.
move=>hm hDelta hIsolated.
have hZero s:structure_plane_radial_supremum m phi A a V delta s=0%E.
  exact:(@structure_isolated_centre_radial_zero R n k m phi A a V delta s
    hm hDelta hIsolated).
exists delta; split=>//; split.
- move=>b hb; exists 1; split; first exact:ltr01.
  by move=>s hs hSmall; rewrite hZero.
- move=>b hb; exists 1; split; first exact:ltr01.
  by move=>s hs hSmall; rewrite hZero.
Qed.
