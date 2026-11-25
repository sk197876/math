(** Federer (1969), 3.2.16, p. 253:
    the countable covering estimate for the set
    omitted by the annular union. The centre
    is treated separately, as in the erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureBasic
  MeasureIndexedCover NonnegativeSum MetricClosedBalls GeometricErrorBudget
  GeometricErrorTailSum MetricDensityAnnularRadii NormAnnularSetUP
  NormAnnularSetGeometry ShrinkingRadiusSelectionUP ShrinkingRadiusSelectionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_annular_omission_mass_bound]:
    the estimate by r^m times a geometric
    tail proving full density of T, Federer
    3.2.16, p. 253. This statement excludes
    the centre so it remains valid at atoms. *)
Theorem norm_annular_omission_mass_bound (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) (mu : set X -> \bar R) m
    (S : nat -> set X) a (rho : nat -> R) (T : set X) J (r : R) :
  is_measure mu ->
  is_shrinking_radius_selection
    (@metric_density_annular_radius_property R (real_norm_metric_space hNX) mu m S a) rho ->
  is_norm_annular_set NX S a rho T -> 0<r<rho J ->
  (mu (((~` T) `\` [set a]) `&` @metric_closed_ball R
    (real_norm_metric_space hNX) a r) <=
    (r^+m*geometric_error_tail (2:R) J)%R%:E)%E.
Proof.
move=> hm hR hT /andP [hr hrJ].
pose M := real_norm_metric_space hNX.
pose F := fun n => ((~` S n) `&` (@metric_closed_ball R M a (Num.min r (rho n)))).
have hF n : (mu (F n)<=(r^+m*geometric_error_budget (2:R) n)%R%:E)%E.
  have hs : 0<Num.min r (rho n) by rewrite lt_min hr (shrinking_radius_positive hR n).
  have hsr : Num.min r (rho n)<=r by rewrite ge_min lexx.
  have hsn : Num.min r (rho n)<=rho n by rewrite ge_min lexx orbT.
  have hpr : 0<Num.min r (rho n)<=rho n by apply/andP; split.
  have hb := shrinking_radius_property hR n _ hpr.
  apply: (le_trans hb _); rewrite lee_fin [r^+m*_]mulrC.
  apply: ler_wpM2l; first exact: ltW (geometric_error_budget_positive n (ltr0n R 2)).
  exact: (lerXn2r m (ltW hs) (ltW hr) hsr).
have hcover : (((~` T) `\` [set a]) `&` @metric_closed_ball R M a r)
    `<=` \bigcup_(n in [set n : nat | (J<=n)%N]) F n.
  move=> x [[hnot hne] hball].
  have hx : NX (x-a)<=r.
    change (is_true (NX (a-x)<=r)) in hball.
    by rewrite (real_seminorm_subtract hNX.1) in hball.
  have hp : 0<NX (x-a).
    rewrite (real_norm_positive hNX.1 hNX.2) subr_eq0.
    apply/eqP=> heq; exact: hne heq.
  have h0 := shrinking_radius_monotone hR (leq0n J).
  have [n [hinner houter]] := shrinking_radius_annulus_index hR hp
    (le_trans hx (le_trans (ltW hrJ) h0)).
  have hJn := norm_annular_index_near_center hR hinner (le_lt_trans hx hrJ).
  exists n; first exact hJn.
  split.
  - move=> hS; apply: hnot; apply: (hT x).2; exists n; by split.
  - change (is_true (NX (a-x)<=Num.min r (rho n))).
    rewrite (real_seminorm_subtract hNX.1) le_min hx houter; reflexivity.
have hcoverbound := @measure_indexed_cover R M _ mu hm
  (((~` T) `\` [set a]) `&` @metric_closed_ball R M a r)
  [set n : nat | (J<=n)%N] F (countableP _) hcover.
apply: (le_trans hcoverbound _).
apply: (le_trans _ (geometric_error_weighted_tail_bound J (exprn_ge0 m (ltW hr)))).
apply: nonnegative_sum_mono=> n _; exact: hF.
Qed.
