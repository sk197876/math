(** Federer (1969), 3.3.19, p. 303: actual
    radial retractions exist with the independent printed
    laws. The proof uses proved compact nearest points
    and Chapter 1 nonexpansion, leaving the auxiliary
    map existential and assuming no Chapter 4 theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  InnerNearestUP InnerClosedBallConvex EuclideanClosedBallCompact CompactNearest InnerNearestContraction
  MetricClosedBalls LipschitzUP RadialBallRetractionUP InnerBallRadialNearest.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_radial_ball_retraction_exists]:
    existence of the original radial f with its
    actual nonexpansion, fixed ball and outward-ray
    formula, 3.3.19, p. 303. Every finite
    ambient dimension and every nonnegative radius are
    retained. No global auxiliary retraction is selected. *)
Theorem euclidean_radial_ball_retraction_exists (R:realType) n
    (z:inner_metric_space (@euclidean_inner_productP R n)) (r:R):
  0<=r ->exists P,@is_radial_ball_retraction R (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) z r P.
Proof.
move=>hr.
pose hE:=@euclidean_inner_productP R n.
pose C:=metric_closed_ball z r.
have hNonempty:C!=set0.
  exists z;change (is_true (mdist z z<=r));by rewrite mdistxx.
have hCompact:=@euclidean_closed_metric_ball_compact R n z r.
have hConvex:=@inner_metric_closed_ball_convex R (R_n R n) (@euclidean_inner_product R n) hE z r.
have hExists x:exists p,is_inner_nearest hE x C p.
  exact:(@compact_inner_nearest_exists R (R_n R n) (@euclidean_inner_product R n) hE
    x C hNonempty hCompact).
have [P hP]:=choice hExists.
have hZeroDistance a b:inner_norm hE (a-b)= 0 ->a=b.
  by move=>/eqP;rewrite inner_norm_eq0 subr_eq0=>/eqP.
exists P;constructor.
- move=>x;exact:inner_nearest_member_law (hP x).
- move=>x hx.
  have hMinimum:=inner_nearest_minimal_law (hP x) hx.
  rewrite subrr inner_norm0 in hMinimum.
  have hZero:inner_norm hE (x-P x)= 0.
    apply/eqP;by rewrite eq_le hMinimum inner_norm_nonnegative.
  exact:esym (hZeroDistance x (P x) hZero).
- split;first exact:ler01.
  move=>x y _ _;rewrite !inner_metric_distanceE mul1r.
  exact:(inner_nearest_pair_nonexpanding hConvex (hP x) (hP y)).
- move=>u d hu hrd.
  have hRay:=@inner_ball_radial_nearest R (R_n R n) (@euclidean_inner_product R n) hE z u r d hu hr hrd.
  have hContraction:=inner_nearest_pair_nonexpanding hConvex (hP (z+d*:u)) hRay.
  rewrite subrr inner_norm0 in hContraction.
  have hZero:inner_norm hE (P (z+d*:u)-(z+r*:u))= 0.
    apply/eqP;by rewrite eq_le hContraction inner_norm_nonnegative.
  exact:hZeroDistance _ _ hZero.
Qed.
