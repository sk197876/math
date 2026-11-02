(** Supporting normed-subspace background for Federer (1969), 2.9.22, p.
    167: pass to the closed separable linear subspace containing the curve
    image. The subspace inherits its norm through the actual linear
    inclusion. This adapter uses the norm laws of 2.4.12, p. 86, and the
    existing arbitrary-dimensional subspace carrier. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import ModuleQuotient SubspaceCarrier RealNormUP RealSeminormOperations
  NormMetric NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [subspace_norm]: supporting restriction of the
    given norm to a vector subspace in Federer 2.9.22,
    p. 167, separable-range reduction. This is the supplied
    ambient norm composed with inclusion, without a new norm
    construction or a choice of coordinates. *)
Definition subspace_norm (R : realType) (E : lmodType R) (N : E -> R)
    (Z : subspace E) (z : subspace_space Z) := N (subspace_val z).
Arguments subspace_norm {R E} N Z z.

(** Source for [subspace_norm_laws]: supporting inherited
    norm laws for the subspace reduction in Federer 2.9.22,
    p. 167. Injectivity and linearity of inclusion preserve
    definiteness, homogeneity and the triangle inequality in
    arbitrary dimension. *)
Lemma subspace_norm_laws (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E) :
  is_real_norm (subspace_norm N Z).
Proof.
exact (@real_norm_injective_precompose R [the lmodType R of subspace_space Z] E
  N hN (@subspace_inclusion R E Z) (@subspace_val_injective R E Z)).
Qed.
Arguments subspace_norm_laws {R E N} hN Z.

(** Source for [subspace_norm_inclusion_distance]: supporting
    isometry of inclusion for Federer 2.9.22, p. 167.
    The inherited metric is exactly the ambient norm distance
    between the included vectors. *)
Lemma subspace_norm_inclusion_distance (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E)
    (x y : real_norm_metric_space (subspace_norm_laws hN Z)) :
  mdist (subspace_val x : real_norm_metric_space hN) (subspace_val y)=mdist x y.
Proof.
rewrite !real_norm_metric_distanceE /subspace_norm.
by rewrite linearB.
Qed.

(** Source for [subspace_norm_derivative_inclusion]: supporting
    transport of actual norm derivatives from the supporting
    subspace to Y in Federer 2.9.22, p. 167. Inclusion
    preserves every difference-quotient norm error, not just
    scalar weak derivatives. *)
Lemma subspace_norm_derivative_inclusion (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E)
    (g : R -> subspace_space Z) (x : R) (v : subspace_space Z) :
  has_normed_curve_derivative (subspace_norm N Z) g x v ->
  has_normed_curve_derivative N (fun t => subspace_val (g t)) x (subspace_val v).
Proof.
move=> hg e he; have [d [hd hB]] := hg e he.
by exists d; split=> // h hh.
Qed.
