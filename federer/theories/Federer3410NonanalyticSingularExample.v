(** Federer (1969), 3.4.10, p. 338:
    an analytic set may have a nonanalytic singular
    part. Verify Cartan's actual polynomial surface from
    Whitney and Bruhat, section 11(c), p. 159.
    Positive axis points are singular and negative axis
    points are regular; the existing analytic identity theorem
    then excludes even an analytic singular-part germ at zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormHigherCurveDerivativeUP NormedPrimitiveCell
  SetGermUP AnalyticVarietyGermUP AnalyticSetDimension AnalyticRegularLocusSealed
  AnalyticHalfLineObstruction BruhatWhitneySurfaceUP BruhatWhitneySurfaceSealed
  BruhatWhitneySurfaceAnalytic BruhatWhitneySurfaceDimension BruhatWhitneyAxis
  BruhatWhitneyPositiveAxisSingular BruhatWhitneyNegativeAxisRegular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_singular_part_not_analytic_germ]:
    the cited original example in 3.4.10, p. 338,
    has a singular part whose germ at zero is
    not an analytic variety germ. No description of
    that singular part is assumed. *)
Theorem bruhat_whitney_singular_part_not_analytic_germ (R:realType):
  let X:=R_n R 3 in
  let NX:=inner_norm (@euclidean_inner_productP R 3) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3) in
  let S:=@BruhatWhitneySurface.set R in
  let D:=S `\` @AnalyticRegularLocus.value R 3 (@analytic_set_dimension R 3 S) setT S in
  ~@is_analytic_variety_germ R X NX hNX 0
    (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 D).
Proof.
move=>X NX hNX S D.
pose e:=@coordinate_basis R 3 ord_max.
pose L:=@scalar_coefficient_linear_map R X e.
apply:(@analytic_half_line_obstruction R X NX hNX D L
  (scalar_coefficient_linear_bound hNX e)).
- move=>t ht;split;first exact:bruhat_whitney_axis_membership.
  exact:bruhat_whitney_positive_axis_singular ht.
- move=>t ht [_ hSingular];apply:hSingular.
  exact:bruhat_whitney_negative_axis_regular ht.
Qed.

(** Source for [federer_3_4_10_nonanalytic_singular_example]:
    the final assertion of 3.4.10, p. 338:
    the singular part of a locally analytic set
    need not be locally analytic. The example has
    the actual original analytic dimension two. *)
Theorem federer_3_4_10_nonanalytic_singular_example (R:realType):
  let X:=R_n R 3 in
  let NX:=inner_norm (@euclidean_inner_productP R 3) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3) in
  exists S:set X,
    @is_analytic_set_in R X NX hNX setT S /\
    @analytic_set_dimension R 3 S= 2%N /\
    ~@is_analytic_set_in R X NX hNX setT
      (S `\` @AnalyticRegularLocus.value R 3 (@analytic_set_dimension R 3 S) setT S).
Proof.
move=>X NX hNX;exists (@BruhatWhitneySurface.set R).
split;first exact:bruhat_whitney_surface_locally_analytic.
split;first exact:bruhat_whitney_surface_dimension.
move=>hAnalytic.
exact:(@bruhat_whitney_singular_part_not_analytic_germ R (hAnalytic 0 Logic.I)).
Qed.
