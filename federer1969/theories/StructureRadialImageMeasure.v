(** Federer (1969), 3.3.4, p. 291: the actual
    radius-supremum image measures psi_v. The public
    pointwise-supremum operator is opaque and specified by
    its order laws. The source of a partial direction
    map is an explicit set D; values outside D are
    irrelevant, and no regularity of psi_v is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealBoundsUP MeasureFamilySupremumUP
  MeasureFamilySupremum MeasureUP MeasureBasic MeasureRestriction
  MeasurePushforward FiniteMeasureScaling StructureConeDensityValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_radial_image_component]: one
    weighted image measure in the displayed supremum
    defining psi_v, Federer 3.3.4, p. 291.
    The original source, strict ball, map domain and
    inverse image are retained as actual sets. *)
Definition structure_radial_image_component (R:realType) (X:metricType R)
    (Y:choiceType) m (phi:set X->\bar R) (A:set X) (a:X)
    (D:set X) (f:X->Y) (r:R) (S:set Y): \bar R:=
  (((r^-1)^+m)%:E * phi [set x|A x /\ (mdist a x<r)%R /\ D x /\ S (f x)]).

(** Source for [structure_radial_image_measure]: the
    actual measure psi_v of Federer 3.3.4, p. 291,
    with a general positive cutoff delta in place of
    1/v. Its value is the independently sealed
    pointwise supremum of the actual component measures. *)
Definition structure_radial_image_measure (R:realType) (X:metricType R)
    (Y:choiceType) m (phi:set X->\bar R) (A:set X) (a:X)
    (D:set X) (f:X->Y) (delta:R):set Y->\bar R:=
  measure_family_supremum [set r:R|(0<r<delta)%R]
    (structure_radial_image_component m phi A a D f).

(** Source for [structure_radial_image_measure_specification]:
    the exact least-upper-bound laws for the original
    displayed radius supremum, Federer 3.3.4, p. 291.
    No statement from the trichotomy is a specification premise. *)
Lemma structure_radial_image_measure_specification (R:realType) (X:metricType R)
    (Y:choiceType) m (phi:set X->\bar R) (A:set X) (a:X)
    (D:set X) (f:X->Y) (delta:R) S:
  is_extended_real_supremum
    [set z|exists r:R,(0<r<delta)%R /\ z=structure_radial_image_component m phi A a D f r S]
    (structure_radial_image_measure m phi A a D f delta S).
Proof. exact:measure_family_supremum_specification. Qed.

(** Source for [structure_radial_image_component_is_measure]:
    each component of psi_v measures the actual target,
    supporting Federer 3.3.4, p. 291, by restriction,
    image and finite positive scaling of 2.1.2, pp. 53–54. *)
Lemma structure_radial_image_component_is_measure (R:realType) (X:metricType R)
    (Y:choiceType) m (phi:set X->\bar R) (A:set X) (a:X)
    (D:set X) (f:X->Y) (r:R):
  is_measure phi ->(0<r)%R ->is_measure (structure_radial_image_component m phi A a D f r).
Proof.
move=>hPhi hr.
have hSource:=measure_restrict_is_measure hPhi [set x|A x /\ (mdist a x<r)%R /\ D x].
have hImage:=measure_pushforward_is_measure f hSource.
have hWeight:(0<=(r^-1)^+m)%R by rewrite exprn_ge0 // invr_ge0; exact:ltW hr.
have hScaled:=finite_scale_is_measure hImage hWeight.
have hEq:(fun S=>(((r^-1)^+m)%:E *
    measure_pushforward f (measure_restrict phi [set x|A x /\ (mdist a x<r)%R /\ D x]) S))=
    structure_radial_image_component m phi A a D f r.
  apply:funext=>S; rewrite /measure_pushforward /measure_restrict /structure_radial_image_component.
  congr (_*_); congr (phi _); apply/seteqP; split=>x.
  - by move=>[[hA [hB hD]] hS]; repeat split.
  - by move=>[hA [hB [hD hS]]]; repeat split.
by rewrite -hEq.
Qed.

(** Source for [structure_radial_image_is_measure]: the
    measure assertion for psi_v in Federer 3.3.4,
    p. 291. The proof retains arbitrary outer measures,
    arbitrary original sources and arbitrary partial-map domains. *)
Theorem structure_radial_image_is_measure (R:realType) (X:metricType R)
    (Y:choiceType) m (phi:set X->\bar R) (A:set X) (a:X)
    (D:set X) (f:X->Y) (delta:R):
  is_measure phi ->(0<delta)%R ->is_measure (structure_radial_image_measure m phi A a D f delta).
Proof.
move=>hPhi hd; apply:measure_family_supremum_is_measure.
- exists (delta/2)%R; exact:structure_density_positive_half_bounds hd.
- move=>r /andP [hr _]; exact:(structure_radial_image_component_is_measure m A a D f hPhi hr).
Qed.
