(** Federer (1969), 2.9.16, p. 161: the counterexample using all closed
    balls containing the base point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanCoordinateMetric EuclideanAffineLineGeometry HausdorffLength HausdorffCoordinateLines
  RealMetricBackground LebesgueScalarMeasure MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic
  MeasureRestriction BorelRegularRestriction MeasureDerivationContext CoveringFamilyUP MetricBoundedUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


Section LineMeasure.
Variable R : realType.
Variable n : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Variable i : 'I_n.
Variable v : E.
Local Notation f := (euclidean_coordinate_line i v).
Local Notation Y := (euclidean_affine_coordinate_line i v).

(** Source for [euclidean_affine_line_measure]: direct choice
    psi=H^1 restricted to Y in Federer 2.9.16,
    p. 161, for the Euclidean coordinate line Y. It
    uses the project's actual Hausdorff-length measure, rather
    than substituting an axiomatically assumed line measure. *)
Definition euclidean_affine_line_measure := measure_restrict (@hausdorff_length R E) Y.

(** Source for [euclidean_affine_line_measure_preimage]: supporting
    computation of psi in Federer 2.9.16, p. 161.
    The isometric line parametrisation identifies its Hausdorff
    measure with scalar Lebesgue measure on the preimage of
    every ambient set, by 2.10.7 and 2.10.11. *)
Lemma euclidean_affine_line_measure_preimage (A : set E) :
  euclidean_affine_line_measure A=lebesgue_scalar_measure (f @^-1` A).
Proof.
rewrite /euclidean_affine_line_measure /measure_restrict.
have he : Y `&` A=f @` (f @^-1` A).
  apply/seteqP; split=> y.
  - by move=> [[t _ <-] ht]; exists t.
  - by move=> [t ht <-]; split=> //; exists t.
by rewrite he hausdorff_coordinate_line_measure.
Qed.

(** Source for [euclidean_affine_line_measure_class]: direct standing-class
    requirement for psi in Federer 2.9.16, p. 161. Borel restriction gives
    Borel regularity, and the inverse image of a bounded ambient set is
    contained in a finite parameter interval. *)
Lemma euclidean_affine_line_measure_class : is_derivation_measure euclidean_affine_line_measure.
Proof.
constructor.
- exact (@measure_restrict_is_measure R E (@hausdorff_length R E)
    (@hausdorff_length_is_measure R E) Y).
- exact (@borel_regular_restrict_borel R E (@hausdorff_length R E)
    (@hausdorff_length_is_measure R E) (@hausdorff_length_borel_regular R E)
    Y (euclidean_affine_coordinate_line_borel i v)).
- move=> A hA; have [b [hb hdist]] := @metric_bounded_distance_bound R E A (f 0%R) hA.
  rewrite euclidean_affine_line_measure_preimage.
  have hsub : f @^-1` A `<=` `[(-b)%R,b].
    move=> t ht; have hd := hdist (f t) ht.
    rewrite euclidean_coordinate_line_distance real_line_metric_distanceE sub0r normrN in hd.
    by rewrite /= in_itv /= -ler_norml.
  have hbound := @measure_mono R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) (f @^-1` A) `[(-b)%R,b] hsub.
  apply: le_lt_trans hbound _.
  rewrite lebesgue_scalar_segment; first exact: ltry.
  lra.
Qed.

(** Source for [euclidean_affine_line_measure_singleton]: supporting zero
    length of the tangent-ball intersection in Federer 2.9.16, p. 161 A
    singleton on Y corresponds to a singleton parameter, of scalar Lebesgue
    measure zero. *)
Lemma euclidean_affine_line_measure_singleton (s : R) :
  euclidean_affine_line_measure [set f s]=0.
Proof.
rewrite euclidean_affine_line_measure_preimage.
have he : f @^-1` [set f s]=[set s].
  apply/seteqP; split=> t /=.
  - move=> h; have hi := can_inj (@euclidean_coordinate_line_retraction R n i v).
    by have := hi _ _ h.
  - by move=> ->.
by rewrite he lebesgue_scalar_singleton.
Qed.

(** Source for [euclidean_affine_line_measure_infinite]: direct
    assertion psi(Y)=infinity in Federer 2.9.16, p. 161.
    Scalar intervals of arbitrarily large length lie in the
    parameter line, so its Lebesgue measure is infinite. *)
Lemma euclidean_affine_line_measure_infinite : euclidean_affine_line_measure Y= +oo.
Proof.
rewrite euclidean_affine_line_measure_preimage.
have he : f @^-1` Y=setT.
  apply/seteqP; split=> t // _; by exists t.
rewrite he; apply/eqP; rewrite -leye_eq.
apply: contrapT=> hn.
have hf : lebesgue_scalar_measure (@setT R) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (lebesgue_scalar_is_measure R) setT)).
  by rewrite ltNge; apply/negP.
pose q := fine (lebesgue_scalar_measure (@setT R)).
have hq : (0<=q)%R.
  have hnon := @measure_nonnegative R R (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) setT.
  by move: hnon; rewrite -(fineK hf) lee_fin.
have hb := @measure_mono R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) `[0%R,(q+1)%R] setT (fun _ _ => I).
rewrite lebesgue_scalar_segment in hb; last by lra.
have hbad : (q+1<=q)%R by move: hb; rewrite subr0 -(fineK hf) -/q lee_fin.
have hstrict : (q<q+1)%R by rewrite ltrDl ltr01.
by have hfalse := lt_le_trans hstrict hbad; rewrite ltxx in hfalse.
Qed.
End LineMeasure.
