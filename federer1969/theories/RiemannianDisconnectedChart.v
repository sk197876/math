(** Federer (1969), 3.2.46, p. 281: on a disconnected chart
    the defining infimum can be infinite. The actual punctured line
    gives a local qualification to the printed finite-metric claim.
    No curve, distance or topological property is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology normedtype lra.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanOneCoordinate RiemannianCurveCost RiemannianDistance
  LipschitzIntervalRetraction StieltjesSubstitution NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_punctured_line_infinite_distance]:
    concrete boundary check of the curve infimum in 3.2.46,
    p. 281. The original open punctured line and both original
    points are retained. A continuous connecting curve would cross
    zero. Thus rho(-1,1)=infinity; a finite metric requires a
    component restriction or the separately proved local carrier. *)
Theorem riemannian_punctured_line_infinite_distance (R:realType):
  let E:=inner_metric_space (@euclidean_inner_productP R 1) in
  let A:set E:=[set x|euclidean_one_project x!=0] in
  open A /\ A (euclidean_one_embed (-1:R)) /\ A (euclidean_one_embed (1:R)) /\
    @riemannian_distance R 1 A (fun _=>@euclidean_inner_product R 1)
      (euclidean_one_embed (-1:R)) (euclidean_one_embed (1:R))= +oo%E.
Proof.
move=>E A.
have hOpen:open A.
  have hEq:A=(@euclidean_one_project R) @^-1` (~`[set (0:R)]).
    apply/seteqP; split=>x hx; first by move=>h; move/eqP:hx; apply.
    apply/eqP; exact hx.
  rewrite hEq.
  have hClosed:@closed (real_line_metric R) [set (0:R)].
    apply:accessible_closed_set1; apply:hausdorff_accessible; exact:metric_hausdorff.
  exact (@open_comp E (real_line_metric R) (@euclidean_one_project R)
    (~`[set (0:R)]) (fun x _=>@euclidean_one_project_continuous R x) (closed_openC hClosed)).
split; first exact hOpen.
split; first by rewrite /A /= euclidean_one_embedK oppr_eq0 oner_eq0.
split; first by rewrite /A /= euclidean_one_embedK oner_eq0.
apply:riemannian_distance_no_curve=>C a b [hab [[L [hL hBound]] [hImage [hStart hEnd]]]].
pose F:=fun t=>C (segment_retraction a b t).
have hGlobal:=@metric_curve_retraction_lipschitz R [the metricType R of E]
  C a b L hab hBound.
have hF:continuous (F:real_line_metric R->E).
  apply:(@metric_fixed_lipschitz_continuous R
    [the metricType R of real_line_metric R] [the metricType R of E] F L hGlobal.1)=>t u.
  exact:hGlobal.2 t u I I.
pose p:=fun t=>euclidean_one_project (F t).
have hp:continuous (p:real_line_metric R->real_line_metric R).
  move=>t; exact:(continuous_comp (hF t) (@euclidean_one_project_continuous R (F t))).
have hAtA:a<=a<=b by rewrite lexx hab.
have hAtB:a<=b<=b by rewrite hab lexx.
have hpa:p a= -1 by rewrite /p /F (segment_retraction_id hAtA) hStart euclidean_one_embedK.
have hpb:p b= 1 by rewrite /p /F (segment_retraction_id hAtB) hEnd euclidean_one_embedK.
have hBounds:Num.min (p a) (p b)<=0<=Num.max (p a) (p b).
  have hOrder:(-1:R)<=1 by lra.
  rewrite hpa hpb min_l // max_r //; apply/andP; split; lra.
have [t ht hpt]:=@IVT R p a b 0 hab (continuous_subspaceT hp) hBounds.
have hAvoid:=@metric_curve_retraction_image R E C A a b hab hImage t.
change (is_true (p t!=0)) in hAvoid.
by rewrite hpt eqxx in hAvoid.
Qed.
