(** Federer (1969), 3.3.4, p. 291: the actual
    psi_v measures decrease with the radial cutoff and
    give zero mass outside the original source image R_v.
    These consequences use only their independent supremum
    laws and the original outer-measure laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealBoundsUP MeasureUP MeasureBasic
  StructureRadialImageMeasure StructureConeDensityValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_radial_image_cutoff_mono]:
    decreasing psi_v in the countable assembly of
    Federer 3.3.4, p. 291. A larger positive
    integer v has a smaller actual radius domain;
    the supporting comparison retains arbitrary real cutoffs. *)
Lemma structure_radial_image_cutoff_mono (R:realType) (X:metricType R)
    (Y:choiceType) m (phi:set X->\bar R) (A:set X) (a:X)
    (D:set X) (f:X->Y) (delta eta:R) S:
  (delta<=eta)%R ->
  structure_radial_image_measure m phi A a D f delta S<=
    structure_radial_image_measure m phi A a D f eta S.
Proof.
move=>hde.
apply:(extended_real_supremum_least (structure_radial_image_measure_specification m phi A a D f delta S)).
move=>z [r [/andP [hr hrd] ->]].
apply:(extended_real_supremum_upper (structure_radial_image_measure_specification m phi A a D f eta S)).
exists r; split=>//; apply/andP; split=>//; exact:lt_le_trans hrd hde.
Qed.

(** Source for [structure_radial_image_original_support_null]:
    psi_v(T(U) minus R_v)=0, Federer 3.3.4,
    p. 291. R_v here is the actual image of
    the original source in its strict cutoff ball
    and actual map domain. No hull or source
    measurability is used in the nullity argument. *)
Theorem structure_radial_image_original_support_null (R:realType) (X:metricType R)
    (Y:choiceType) m (phi:set X->\bar R) (A:set X) (a:X)
    (D:set X) (f:X->Y) (delta:R):
  is_measure phi ->(0<delta)%R ->
  structure_radial_image_measure m phi A a D f delta
    (~` (f @` [set x|A x /\ (mdist a x<delta)%R /\ D x]))=0.
Proof.
move=>hPhi hd.
pose S:=~` (f @` [set x|A x /\ (mdist a x<delta)%R /\ D x]).
have hEmpty r (hr:(0<r<delta)%R):
    [set x|A x /\ (mdist a x<r)%R /\ D x /\ S (f x)]=set0.
  apply/seteqP; split=>x; last by [].
  move=>[hA [hBall [hD hS]]]; apply:hS.
  exists x=>//; split=>//; split=>//; exact:lt_trans hBall (andP hr).2.
have hZero r (hr:(0<r<delta)%R):structure_radial_image_component m phi A a D f r S=0.
  by rewrite /structure_radial_image_component (hEmpty r hr) (measure_empty hPhi) mule0.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:(extended_real_supremum_least (structure_radial_image_measure_specification m phi A a D f delta S)).
  by move=>z [r [hr ->]]; rewrite (hZero r hr).
- have hr:=structure_density_positive_half_bounds hd.
  rewrite -(hZero (delta/2)%R hr).
  apply:(extended_real_supremum_upper (structure_radial_image_measure_specification m phi A a D f delta S)).
  by exists (delta/2)%R.
Qed.

(** Source for [structure_radial_original_images_decrease]:
    the actual R_v sets decrease with v,
    Federer 3.3.4, p. 291. Only the strict
    source-ball cutoff changes; the original map and
    its domain are retained. *)
Lemma structure_radial_original_images_decrease (R:realType) (X:metricType R)
    (Y:Type) (A:set X) (a:X) (D:set X) (f:X->Y) (delta eta:R):
  (delta<=eta)%R ->
  f @` [set x|A x /\ (mdist a x<delta)%R /\ D x] `<=`
    f @` [set x|A x /\ (mdist a x<eta)%R /\ D x].
Proof.
move=>hde y [x [hA [hNear hD]] <-]; exists x=>//.
split=>//; split=>//; exact:lt_le_trans hNear hde.
Qed.
