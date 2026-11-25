(** Federer (1969), 1.6.6, p. 27: sign(r) is determined by the complex
    simple vector, and positivity means r>0. These statements compare
    arbitrary paired representations, not merely a preselected basis. Source
    context are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleElementary ScalarRestriction
  ComplexScalarSealed ComplexPairedVectors ComplexPlaneOrientation ComplexSimpleVectors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Signs.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Variable V : lmodType C.
Local Notation VR := (restricted_space (ComplexScalars.embed R) V).

(** Source for [paired_representation_sign]: Federer 1.6.6,
    p. 27, uniqueness of sign(r). Equal nonzero real multiples of
    paired products have scalar coefficients of the same sign. *)
Theorem paired_representation_sign p (v w : 'I_p -> V) (r s : R) :
  r *: paired_complex_vector v != 0 ->
  r *: paired_complex_vector v = s *: paired_complex_vector w -> Num.sg r = Num.sg s.
Proof.
move=> hx h.
have /andP [hr hv] : (r != 0) && (paired_complex_vector v != 0).
  by move: hx; rewrite scaler_eq0 negb_or.
have /andP [hs hw] : (s != 0) && (paired_complex_vector w != 0).
  by move: hx; rewrite h scaler_eq0 negb_or.
have heq z : FedererSimple.T (paired_complex_vector v) z <-> FedererSimple.T (paired_complex_vector w) z.
  have ht : FedererSimple.T (r *: paired_complex_vector v) z <->
    FedererSimple.T (s *: paired_complex_vector w) z by rewrite h.
  rewrite (@associated_scale_nonzero R VR (p+p) (paired_complex_vector v) r hr)
    (@associated_scale_nonzero R VR (p+p) (paired_complex_vector w) s hs) in ht.
  exact ht.
have [d [hd hwv]] := paired_planes_positive_multiple hv hw heq.
have hrs : r = s*d.
  apply: (nonzero_vector_scalar_injective hv).
  by rewrite -[RHS]scalerA -hwv.
by rewrite hrs sgrM (gtr0_sg hd) mulr1.
Qed.

(** Source for [complex_pair_count_unique]: Federer 1.6.6,
    p. 27, m=2p. The number of real-imaginary pairs is uniquely
    determined by the real degree. *)
Lemma complex_pair_count_unique m p q : m = (p+p)%N -> m = (q+q)%N -> p = q.
Proof. move=> hp hq; apply: double_inj; by rewrite -!addnn -hp -hq. Qed.

(** Source for [complex_representation_sign]: Federer 1.6.6,
    p. 27, sign(r) is uniquely determined by xi. Full comparison
    of two arbitrary paired representations of the same nonzero
    real m-vector, allowing the pair counts to be given separately. *)
Theorem complex_representation_sign m (xi : exterior_power VR m)
  p q (v : 'I_p -> V) (w : 'I_q -> V) (r s : R) :
  xi != 0 -> m = (p+p)%N -> m = (q+q)%N ->
  component_val xi = r *: component_val (paired_complex_vector v) ->
  component_val xi = s *: component_val (paired_complex_vector w) -> Num.sg r = Num.sg s.
Proof.
move=> hx hp hq hr hs.
have hpq := complex_pair_count_unique hp hq; subst q; subst m.
have hrv : xi = r *: paired_complex_vector v by apply: val_inj; rewrite linearZ.
have hsw : xi = s *: paired_complex_vector w by apply: val_inj; rewrite linearZ.
apply: (@paired_representation_sign p v w r s); [by rewrite -hrv | by rewrite -hrv -hsw].
Qed.

(** Source for [positive_complex_vector]: Federer 1.6.6,
    p. 27, final definition: a complex simple vector is positive
    when its real coefficient r in a paired representation is positive. *)
Definition positive_complex_vector m (xi : exterior_power VR m) :=
  complex_simple_vector xi /\
  exists p, exists v : 'I_p -> V, exists r : R,
    m = (p+p)%N /\ 0 < r /\
    component_val xi = r *: component_val (paired_complex_vector v).

(** Source for [positive_complex_vector_iff]: Federer 1.6.6,
    p. 27, positivity is independent of the paired representation.
    In every representation of a complex simple vector, positivity
    holds exactly when its scalar coefficient is positive. *)
Theorem positive_complex_vector_iff m (xi : exterior_power VR m)
  p (v : 'I_p -> V) (r : R) :
  complex_simple_vector xi -> m = (p+p)%N ->
  component_val xi = r *: component_val (paired_complex_vector v) ->
  (positive_complex_vector xi <-> 0 < r).
Proof.
move=> hc hm hr; split.
- move=> [_ [q [w [s [hq [hs hsw]]]]]].
  have hsign := complex_representation_sign (proj1 hc) hm hq hr hsw.
  by rewrite -sgr_gt0 hsign sgr_gt0.
- move=> hpos; split=> //; exists p, v, r; by [].
Qed.
End Signs.
