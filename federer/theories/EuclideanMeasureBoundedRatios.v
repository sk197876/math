(** Federer (1969), 2.10.6, p. 174:
    every pair in the first comparison group has
    a finite uniform multiplicative bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure ExteriorMeasure IntegralGeometricMeasure
  ProjectionBeta EuclideanBallVolume JungConstant MeasureUP EuclideanMeasureComparisonDiagram
  EuclideanMeasureComparisonQuantitative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_first_euclidean_comparison_measure]:
    the four-member group whose ratios are bounded
    in Federer 2.10.6, p. 174:
    spherical, Hausdorff, exterior-diameter and Q_t.
    This predicate specifies membership among the existing
    independently defined measures; it selects no new
    measure or representation. *)
Definition is_first_euclidean_comparison_measure (R : realType) n m (hMN : (m<=n)%N)
    (t : \bar R)
    (mu : set (inner_metric_space (@euclidean_inner_productP R n))->\bar R) : Prop :=
  mu=@spherical_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m \/
  mu=@hausdorff_measure R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m \/
  mu=@exterior_diameter_measure R n m \/mu=@convex_integral_geometric_measure R n m hMN t.

(** Source for [federer_2_10_6_bounded_ratios]:
    direct bounded-ratio assertion for the first group
    in Federer 2.10.6, p. 174.
    The original explicit bounds give a common
    positive finite factor for both comparisons through
    H^m. Their product controls every ordered
    pair in the group, uniformly over every
    target. This multiplication formulation retains zero
    and infinite masses and implies the ratio
    bound whenever the book's ordinary quotient exists.
    No quotient with zero denominator is introduced. *)
Theorem federer_2_10_6_bounded_ratios (R : realType) n m (hMN : (m<=n)%N) (t : \bar R) :
  (0<m)%N ->1<=t ->exists c : R, (0<c)%R /\
  forall mu nu, is_first_euclidean_comparison_measure hMN t mu ->
    is_first_euclidean_comparison_measure hMN t nu ->
    forall A, mu A<=c%:E*nu A.
Proof.
move=> hM hT.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose S := @spherical_measure R [the metricType R of X] m.
pose H := @hausdorff_measure R [the metricType R of X] m.
pose T := @exterior_diameter_measure R n m.
pose Q := @convex_integral_geometric_measure R n m hMN t.
pose b := @projection_beta R n m hMN t.
pose j : R := ((@jung_factor R n)^+m)%R.
pose e : R := ((Num.sqrt n%:R)^+m*2^+m.-1)%R.
pose d : R := ((euclidean_unit_ball_volume R m/(2:R)^+m)*(m`!)%:R)%R.
have hB : (0<b)%R := @projection_beta_positive R n m hMN t hT.
have hJ : (0<=j)%R.
  apply: exprn_ge0; exact: jung_factor_nonnegative.
have hE : (0<=e)%R.
  apply: mulr_ge0; apply: exprn_ge0; [exact: sqrtr_ge0|exact: ler0n].
have hD : (0<=d)%R.
  apply: mulr_ge0; last exact: ler0n.
  apply: divr_ge0; first exact: ltW (euclidean_unit_ball_volumeE R m).2.
  apply: exprn_ge0; exact: ler0n.
have hED : (0<=e*d)%R := mulr_ge0 hE hD.
have hInverse : (0<=b^-1)%R by rewrite invr_ge0; exact: ltW hB.
pose r : R := (1+j+e+e*d+b^-1)%R.
have hR : (0<r)%R by rewrite /r; lra.
have hR1 : (1<=r)%R by rewrite /r; lra.
have hRJ : (j<=r)%R by rewrite /r; lra.
have hRE : (e<=r)%R by rewrite /r; lra.
have hRED : (e*d<=r)%R by rewrite /r; lra.
have hRInverse : (b^-1<=r)%R by rewrite /r; lra.
have hHNonnegative A : 0<=H A := @measure_nonnegative R _ H (@hausdorff_measure_is_measure R _ m) A.
have hQNonnegative A : 0<=Q A := @measure_nonnegative R _ Q
  (@convex_integral_geometric_measure_is_measure R n m hMN t hT) A.
have hUpper mu : is_first_euclidean_comparison_measure hMN t mu ->forall A,mu A<=r%:E*H A.
  move=> hMu A.
  have hDiagram := @federer_2_10_6_comparison_diagram R n m hMN t A hT.
  have hQuantitative := @federer_2_10_6_quantitative_comparisons R n m hMN t A hM hT.
  have hH : H A<=r%:E*H A.
    have hh := lee_wpmul2r (hHNonnegative A) (lee_tofin hR1).
    by rewrite mul1e in hh.
  case: hMu=> [->|[->|[->|->]]].
  - exact: le_trans hQuantitative.1 (lee_wpmul2r (hHNonnegative A) (lee_tofin hRJ)).
  - exact hH.
  - exact: le_trans hDiagram.2.1 hH.
  - have hNormalized : b%:E*Q A<=H A.
      exact: le_trans hDiagram.2.2.2.2.2.2.1
        (le_trans hDiagram.2.2.1 hDiagram.2.1).
    have hScaled := lee_wpmul2l (lee_tofin hInverse) hNormalized.
    rewrite muleA -EFinM mulVf ?(gt_eqF hB) // mul1e in hScaled.
    exact: le_trans hScaled (lee_wpmul2r (hHNonnegative A) (lee_tofin hRInverse)).
have hLower nu : is_first_euclidean_comparison_measure hMN t nu ->forall A,H A<=r%:E*nu A.
  move=> hNu A.
  have hDiagram := @federer_2_10_6_comparison_diagram R n m hMN t A hT.
  have hQuantitative := @federer_2_10_6_quantitative_comparisons R n m hMN t A hM hT.
  have hHToS : H A<=S A := hDiagram.1.
  case: hNu=> [->|[->|[->|->]]].
  - have hSNonnegative : 0<=S A := @measure_nonnegative R _ S (@spherical_measure_is_measure R _ m) A.
    have hh := lee_wpmul2r hSNonnegative (lee_tofin hR1).
    rewrite mul1e in hh; exact: le_trans hHToS hh.
  - have hh := lee_wpmul2r (hHNonnegative A) (lee_tofin hR1).
    by rewrite mul1e in hh.
  - have hTNonnegative : 0<=T A := @measure_nonnegative R _ T (@exterior_diameter_measure_is_measure R n m) A.
    exact: le_trans (le_trans hHToS hQuantitative.2.1)
      (lee_wpmul2r hTNonnegative (lee_tofin hRE)).
  - have h := lee_wpmul2l (lee_tofin hE) hQuantitative.2.2.
    rewrite muleA -EFinM in h.
    exact: le_trans (le_trans hHToS (le_trans hQuantitative.2.1 h))
      (lee_wpmul2r (hQNonnegative A) (lee_tofin hRED)).
exists (r*r)%R; split; first exact (mulr_gt0 hR hR).
move=> mu nu hMu hNu A.
have h := lee_wpmul2l (lee_tofin (ltW hR)) (hLower nu hNu A).
rewrite muleA -EFinM in h.
exact: le_trans (hUpper mu hMu A) h.
Qed.
