(** Federer (1969), 3.3.17, pp. 300–301: the ORIGINAL
    small-cone-density hypothesis, with its exact aperture factor. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient EuclideanInnerProduct InnerMetric
  StructureCone RectifiableSetUP MetricDensities MeasureRestriction MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_small_cone_constant]: the exact
    printed c= 2 inverse times 84 to power minus m in Federer
    3.3.17, p. 300. It is independent of all sources, points,
    apertures and selected planes. *)
Definition structure_small_cone_constant (R:realType) m:R:=(2*84^+m)^-1.

(** Source for [structure_small_cone_constant_positive]:
    supporting positivity of the printed coefficient in Federer
    3.3.17, p. 300, including the natural degree-zero extension. *)
Lemma structure_small_cone_constant_positive (R:realType) m:
  0<structure_small_cone_constant R m.
Proof. rewrite /structure_small_cone_constant invr_gt0; apply:mulr_gt0; by rewrite ?exprn_gt0 // ltr0n. Qed.

(** Source for [structure_small_cone_coefficient_cancel]: the
    reciprocal coefficient converts the 3.3.6 upper-density
    bound into c times upper density at most lambda, in the
    proof of Federer 3.3.17, p. 300. *)
Lemma structure_small_cone_coefficient_cancel (R:realType) m (lam:R):
  structure_small_cone_constant R m*(2*84^+m*lam)=lam.
Proof.
have hK:0<(2*84^+m:R) by apply:mulr_gt0; by rewrite ?exprn_gt0 // ltr0n.
by rewrite /structure_small_cone_constant mulrA mulVf ?gt_eqF // mul1r.
Qed.

(** Source for [structure_small_cone_density_at]: the exact
    pointwise hypothesis of Federer 3.3.17, p. 300. Some original
    (n-m)-plane and 0<s<1 make the upper density of the original
    E intersect X(a,infinity,V,s) strictly below c*s^m times
    the original upper density of phi restricted to E. The
    APERTURE FACTOR s^m is retained. Infinite upper densities
    are allowed and no tangent or rectifiable carrier is supplied. *)
Definition structure_small_cone_density_at (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n)):Prop:=
  exists V:G (R_n R n) (n-m),exists s:R,(0<s<1)%R /\
    (upper_metric_density m (measure_restrict phi (E `&` structure_cone V a +oo s)) a<
      (structure_small_cone_constant R m*s^+m)%:E*
        upper_metric_density m (measure_restrict phi E) a)%E.

(** Source for [is_structure_small_cone_density_criterion]:
    the phi almost-everywhere version of the printed hypothesis
    of Federer 3.3.17, p. 300. The original source E need not be
    measurable. This definition contains only the hypothesis;
    the rectifiability conclusion must be proved separately. *)
Definition is_structure_small_cone_density_criterion (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):Prop:=
  measure_almost_everywhere_on phi E [set a|structure_small_cone_density_at m phi E a].
