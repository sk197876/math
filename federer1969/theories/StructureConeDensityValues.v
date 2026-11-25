(** Federer (1969), 3.3.2, pp. 287–288: supporting
    exact zero and infinite density values from the independent
    order laws. These estimates keep nonempty scale domains
    explicit and are used by actual boundary regressions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  ExtendedRealBoundsUP StructureConeDensityUP StructureConeDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_density_positive_half_bounds]:
    supporting a nonempty positive radius/aperture domain
    in Federer 3.3.2, pp. 287–288. Half of any
    positive real number is strictly between zero and it. *)
Lemma structure_density_positive_half_bounds (R:realType) (t:R):
  0<t ->0<t/2<t.
Proof.
move=>ht; apply/andP; split; first by rewrite divr_gt0 // ltr0n.
have hTwo:0<(2:R) by rewrite ltr0n.
by rewrite (ltr_pdivrMr _ _ hTwo) -{1}[t]mulr1 (ltr_pM2l ht) ltr1n.
Qed.

(** Source for [structure_cone_density_constant_cost]: a
    supporting exact constant-value consequence of the
    upper-limit formula of Federer 3.3.2, pp. 287–288.
    Every positive cutoff has an actual radius/aperture
    witness; infinite constants are permitted. *)
Theorem structure_cone_density_constant_cost (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (delta:R) z (c: \bar R):
  0<delta ->
  (forall r s,0<r<delta ->0<s ->structure_cone_cost hmn phi A z r s=c) ->
  structure_cone_density hmn phi A delta z=c.
Proof.
move=>hDelta hConst.
have hRadius:0<delta/2<delta:=structure_density_positive_half_bounds hDelta.
have hTail t (ht:0<t):is_structure_cone_tail_supremum hmn phi A delta z t c.
  constructor.
  - move=>v [r [s [hr [hs ->]]]]; rewrite (hConst r s hr (andP hs).1); exact:lexx.
  - move=>b hBound.
    have hAperture:0<t/2<t:=structure_density_positive_half_bounds ht.
    rewrite -(hConst (delta/2) (t/2) hRadius (andP hAperture).1).
    apply:hBound; by exists (delta/2),(t/2).
have h:=@structure_cone_density_specification R n m hmn phi A delta z.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact:(h.1 1 c ltr01 (hTail 1 ltr01)).
- apply:h.2=>t q ht hq.
  have he:c=q:=extended_real_supremum_unique (hTail t ht) hq.
  by rewrite he.
Qed.

(** Source for [structure_cone_density_infinite_fixed_radius]:
    the infinite-value case retained by the formula of
    Federer 3.3.2, pp. 287–288. An actual fixed
    admissible radius with infinite cost at every positive
    aperture forces the original upper limit to infinity. *)
Theorem structure_cone_density_infinite_fixed_radius (R:realType) n m
    (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (A:set (inner_metric_space (@euclidean_inner_productP R n)))
    (delta r:R) z:
  0<r<delta ->
  (forall s,0<s ->structure_cone_cost hmn phi A z r s=+oo%E) ->
  structure_cone_density hmn phi A delta z=+oo%E.
Proof.
move=>hr hInfinite; apply/eqP; rewrite eq_le leey /=.
have h:=@structure_cone_density_specification R n m hmn phi A delta z.
apply:h.2=>t q ht hq.
have hAperture:0<t/2<t:=structure_density_positive_half_bounds ht.
rewrite -(hInfinite (t/2) (andP hAperture).1).
apply:(extended_real_supremum_upper hq); by exists r,(t/2).
Qed.
