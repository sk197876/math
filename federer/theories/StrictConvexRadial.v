(** Federer 2.8.9, p. 146, strict-convexity parenthesis: every point
    satisfying the two actual metric radial equations is unique. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  reals topology.
From Federer Require Import RealNormUP NormMetric DirectionalLimitationUP
  StrictConvexNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_midpoint_complements]: Federer 2.8.9, p. 146;
    a vector is the sum of the midpoint of two proposed radial vectors
    and the midpoint of their complementary vectors. Supporting identity. *)
Lemma norm_midpoint_complements (R : realFieldType) (V : lmodType R)
    (u v b : V) : norm_midpoint u v + norm_midpoint (b-u) (b-v) = b.
Proof.
have h : (u+v)+((b-u)+(b-v)) = b+b.
  by rewrite addrACA [u+(b-u)]addrC [v+(b-v)]addrC !subrK.
rewrite /norm_midpoint -scalerDr h scalerDr -scalerDl norm_half_sum_one.
exact: scale1r.
Qed.

(** Source for [strict_convex_equal_radius_unique]: Federer 2.8.9,
    p. 146; supporting norm-space form of radial uniqueness. Two equal
    radius vectors at equal complementary distance from b must agree.
    All radii, including zero, are retained without a normalization choice. *)
Lemma strict_convex_equal_radius_unique (R : realFieldType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (hstrict : is_strictly_convex_norm N)
    (u v b : V) (r : R) :
  N u = r -> N v = r -> N (b-u) = N b-r -> N (b-v) = N b-r -> u = v.
Proof.
move=> hu hv hbu hbv; apply: contrapT=> hne.
have hs : N (norm_midpoint u v) < r by rewrite -hu; apply: hstrict=> //; rewrite hu hv.
have hc : N (norm_midpoint (b-u) (b-v)) <= N b-r.
  rewrite /norm_midpoint (real_seminorm_scale hN.1)
    (gtr0_norm (@positive_norm_half R)).
  have h : (2:R)^-1 * N ((b-u)+(b-v)) <=
      (2:R)^-1 * (N (b-u)+N (b-v)).
    rewrite (ler_pM2l (@positive_norm_half R)); exact: (real_seminorm_triangle hN.1 (b-u) (b-v)).
  by rewrite hbu hbv norm_half_double in h.
have ht := real_seminorm_triangle hN.1 (norm_midpoint u v)
  (norm_midpoint (b-u) (b-v)).
rewrite norm_midpoint_complements in ht.
have h := le_lt_trans ht (ltr_leD hs hc).
by rewrite addrC subrK ltxx in h.
Qed.

(** Source for [strict_convex_radial_projection_unique]: Federer 2.8.9,
    p. 146: for a strictly convex norm the point x in the two radial
    distance equations is uniquely determined by a,b,c. The actual metric
    equations are used; no radial selection or uniqueness is assumed. *)
Theorem strict_convex_radial_projection_unique (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (hstrict : is_strictly_convex_norm N)
    (a b c x y : real_norm_metric_space hN) :
  is_radial_projection_configuration a b c x ->
  is_radial_projection_configuration a b c y -> x = y.
Proof.
move=> [_ [hx hxb]] [_ [hy hyb]].
have h : x-a = y-a.
  apply: (@strict_convex_equal_radius_unique R V N hN hstrict
    (x-a) (y-a) (b-a) (N (c-a))).
  - by move: hx; rewrite !real_norm_metric_distanceE
      !(real_seminorm_subtract hN.1 a).
  - by move: hy; rewrite !real_norm_metric_distanceE
      !(real_seminorm_subtract hN.1 a).
  - have he : (b-a)-(x-a) = b-x by rewrite opprB !addrA subrK.
    rewrite he; move: hxb; rewrite !real_norm_metric_distanceE
      (real_seminorm_subtract hN.1 x) !(real_seminorm_subtract hN.1 a).
    exact: id.
  - have he : (b-a)-(y-a) = b-y by rewrite opprB !addrA subrK.
    rewrite he; move: hyb; rewrite !real_norm_metric_distanceE
      (real_seminorm_subtract hN.1 y) !(real_seminorm_subtract hN.1 a).
    exact: id.
by apply: (addIr (-a)); exact: h.
Qed.

From Federer Require Import NormDirections InnerProductUP InnerNorm
  InnerNormInequalities InnerMetric.

(** Source for [strict_convex_radial_projection_exists_unique]: Federer
    2.8.9, p. 146; combine the proved actual normed radial existence with
    strict-convexity uniqueness under the printed noncentral hypotheses. *)
Theorem strict_convex_radial_projection_exists_unique (R : realType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hstrict : is_strictly_convex_norm N)
    (a b c : real_norm_metric_space hN) :
  b <> a -> c <> a -> mdist a c <= mdist a b ->
  exists x, is_radial_projection_configuration a b c x /\
    forall y, is_radial_projection_configuration a b c y -> y = x.
Proof.
move=> hba hca horder.
have [x [hx _]] := @norm_radial_projection R V N hN a b c hba hca horder.
exists x; split=> // y hy.
exact: (@strict_convex_radial_projection_unique R V N hN hstrict a b c y x hy hx).
Qed.

(** Source for [inner_product_radial_projection_unique]: Federer 2.8.9,
    p. 146, "in particular if v comes from an inner product". The actual
    opaque inner norm and original inner metric discharge strict convexity;
    no strict-convexity assumption is added to this inner-product result. *)
Theorem inner_product_radial_projection_unique (R : realType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    (a b c x y : inner_metric_space hB) :
  is_radial_projection_configuration a b c x ->
  is_radial_projection_configuration a b c y -> x = y.
Proof.
move=> hx hy.
have hN : is_real_norm (inner_norm hB).
  split.
  - split; [exact: inner_norm_nonnegative | exact: inner_normZ | exact: inner_norm_triangle].
  - move=> v hv; apply/eqP; by rewrite -(inner_norm_eq0 hB) hv eqxx.
have hx' : @is_radial_projection_configuration R (real_norm_metric_space hN) a b c x.
  by move: hx; rewrite /is_radial_projection_configuration
    !real_norm_metric_distanceE ?inner_metric_distanceE.
have hy' : @is_radial_projection_configuration R (real_norm_metric_space hN) a b c y.
  by move: hy; rewrite /is_radial_projection_configuration
    !real_norm_metric_distanceE ?inner_metric_distanceE.
exact: (@strict_convex_radial_projection_unique R V (inner_norm hB) hN
  (@canonical_inner_norm_strictly_convex R V B hB) a b c x y hx' hy').
Qed.
