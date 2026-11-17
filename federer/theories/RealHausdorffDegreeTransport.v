(** Federer 2.10.2, p. 171, used in 2.10.27 and 2.10.45,
    pp. 190-191 and 202-203: equal real degrees give the same original
    normalized costs and measures, independently of positivity proofs. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import RealHausdorffNormalisation RealHausdorffMeasure EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_hausdorff_normalisation_equal_degree]: supporting
    scalar transport for Federer 2.10.27 and 2.10.45, pp. 190-191 and
    202-203. Equal degree parameters have equal actual Gamma values. *)
Lemma real_hausdorff_normalisation_equal_degree (R : realType) (p q : R)
    (hp : 0 <= p) (hq : 0 <= q) : p = q ->
    real_hausdorff_normalisation hp = real_hausdorff_normalisation hq.
Proof.
move=> h; subst q.
by rewrite /real_hausdorff_normalisation
  (euler_gamma_proof_irrelevant (real_dimension_gamma_parameter hp)
    (real_dimension_gamma_parameter hq)).
Qed.

(** Source for [real_hausdorff_measure_equal_degree]: supporting
    equality of the original Hausdorff measures at equal real degrees
    in Federer 2.10.27 and 2.10.45, pp. 190-191 and 202-203.
    Every subset, including infinite-mass subsets, is retained. *)
Lemma real_hausdorff_measure_equal_degree (R : realType) (X : metricType R)
    (p q : R) (hp : 0 <= p) (hq : 0 <= q) : p = q -> forall A,
    @real_hausdorff_measure R X p hp A = @real_hausdorff_measure R X q hq A.
Proof.
move=> h; subst q.
by rewrite /real_hausdorff_measure
  (real_hausdorff_normalisation_equal_degree hp hq (erefl p)).
Qed.

(** Source for [real_spherical_measure_equal_degree]: supporting
    equality of the original spherical measures at equal real degrees
    in Federer 2.10.27, pp. 190-191. Positive-radius generators and
    all zero-degree conventions are unchanged. *)
Lemma real_spherical_measure_equal_degree (R : realType) (X : metricType R)
    (p q : R) (hp : 0 <= p) (hq : 0 <= q) : p = q -> forall A,
    @real_spherical_measure R X p hp A = @real_spherical_measure R X q hq A.
Proof.
move=> h; subst q.
by rewrite /real_spherical_measure
  (real_hausdorff_normalisation_equal_degree hp hq (erefl p)).
Qed.
