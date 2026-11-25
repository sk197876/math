(** Federer (1969), 3.2.17, pp. 254–255:
    relative differentiability of F from that
    of F composed with psi. The relative
    derivative is a partial map on the
    tangent plane, and its composite with
    Dpsi is exactly the total composite differential. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealNormUP NormMetric HilbertFormCompactness NormDifferentialUP NormDifferentialLinear
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  PartialFunctionPrecomposition PartialFunctionExtensionality
  MeasureSetDensity CenteredBallRelations EuclideanLebesgueDimensions
  TangentConeUP RelativeDifferentialUP RelativeApproximationCriterion
  MetricBiLipschitzUP EuclideanInjectiveRetraction
  NormRelativeCompositeRemainder EuclideanBiLipschitzOrdinaryPlane.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_bilipschitz_relative_composite]:
    the "Moreover" conclusion and exact
    differential identity of Federer 3.2.17,
    pp. 254–255. A general normed
    target is allowed in this supporting
    theorem; its Euclidean specialization is printed. *)
Theorem euclidean_bilipschitz_relative_composite (R : realType) m n
    (Z : lmodType R) (NZ : Z -> R) (hNZ : is_real_norm NZ)
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n)
    (F : R_n R n -> Z) (lambda : R) a
    (L : Hom (R_n R m) (R_n R n)) (H : Hom (R_n R m) Z) :
  @is_metric_bilipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) K psi lambda ->
  0<lambda -> K a -> injective L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT psi a L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NZ
    setT (fun x=>F (psi x)) a H ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) (~` K)) a 0%E ->
  exists d : partial_function (R_n R n) Z,
    @has_relative_norm_differential R (R_n R n) Z
      (inner_norm (@euclidean_inner_productP R n)) NZ
      (inner_norm_real_norm (@euclidean_inner_productP R n)) setT (psi @` K) F (psi a) d /\
    partial_function_precompose L d=partial_function_total H.
Proof.
move=> hB hLam ha hi hPsi hComp hFull.
pose X := R_n R m; pose Y := R_n R n.
pose NX := inner_norm (@euclidean_inner_productP R m).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
have [P [hP hPL]] := euclidean_injective_bounded_left_inverse hi.
pose Q := hom_comp H P.
have hQ : norm_bounded_linear NY NZ Q.
  exact: norm_bounded_linear_compose hP (norm_differential_bounded hComp).
have hQL v : Q (L v)=H v by rewrite /Q hom_compE hPL.
have hInv x (hx : K x) : NX (x-a)<=lambda*NY (psi x-psi a).
  exact: hB.2 x a hx ha.
have hFirst := @norm_relative_composite_first_order R X Y Z NX NY NZ hNX hNY hNZ
  K psi F a L H Q lambda hPsi hComp hQ hQL hLam ha hInv.
pose W := psi @` K.
pose d := partial_function_source_restrict (norm_tangent_cone NY W (psi a)) (partial_function_total Q).
have hcl : @closure (real_norm_metric_space hNY) W (psi a).
  apply: subset_closure; by exists a.
have hRel : @has_relative_norm_differential R Y Z NY NZ hNY setT W F (psi a) d.
  apply: (@relative_norm_differential_remainder_criterion R Y Z NY NZ hNY hNZ
    setT W F (psi a) d hcl).2.
  exists (F (psi a)),Q; split=> //; by move=> v z.
have hTan := euclidean_bilipschitz_ordinary_tangent_plane hB hLam ha hi hPsi hFull.
exists d; split=> //.
apply: partial_function_graph_extensionality=> v z.
change (norm_tangent_cone NY W (psi a) (L v) /\ Q (L v)=z <-> H v=z).
split.
- by move=> [_ heq]; rewrite -hQL.
- move=> heq; split; last by rewrite hQL.
  rewrite hTan; by exists v.
Qed.
