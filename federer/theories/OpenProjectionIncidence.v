(** Supporting incidence openness for the continuity assertion in Federer
    (1969), 2.10.5(2), p. 173. Federer cites 3.2.36, p. 272, whose actual
    statement gives joint volume continuity on nonempty compact convex sets
    using 3.2.35 and 2.10.33. Here prove the needed open-set step directly
    using exact-length lifts from 1.7.4, p. 30, and joint evaluation
    continuity. This is a supporting proof route, not the whole theorem
    3.2.36. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeIncidence
  ProjectionImageLifting MetricClosedBalls MetricPairDistance TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_incidence_open]: supporting
    openness of {(y,p):y in p(S)} when S is
    open, for Federer 2.10.5(2), p. 173.
    Convexity and boundedness are not needed for
    this intermediate topological assertion. *)
Theorem projection_incidence_open (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  open S -> @open (inner_metric_space (@euclidean_inner_productP R m) *
    euclidean_projection_space R n m)%type (projection_incidence (m:=m) S).
Proof.
move=> hS.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose P := euclidean_projection_space R n m.
rewrite openE.
move=> z hz.
change (exists x : E, S x /\ z.1=euclidean_projection_linear z.2 x) in hz.
have [x [hx hxy]] := hz.
clear hz.
case: z hxy=> [y p] hxy.
have hn : nbhs x S by rewrite openE in hS; exact: hS x hx.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP x S) hn.
pose F (z : Y*P) : Y*Y := (euclidean_projection_linear z.2 x,z.1).
have hF : continuous F.
  have hp : continuous (fun z : Y*P => (z.2,x)).
    exact (@topological_pair_continuous (Y*P)%type P E (@snd Y P) (fun _ => x)
      (@second_projection_continuous Y P) (@cst_continuous (Y*P)%type E x)).
  have hfirst : continuous (fun z : Y*P => (euclidean_projection_linear z.2 x:Y)).
    move=> z; exact (continuous_comp (hp z)
      (@euclidean_projection_evaluation_continuous R n m (z.2,x))).
  exact (@topological_pair_continuous (Y*P)%type Y Y
    (fun z : Y*P => euclidean_projection_linear z.2 x) (@fst Y P)
    hfirst (@first_projection_continuous Y P)).
pose d (z : Y*P) : real_line_metric R := mdist (euclidean_projection_linear z.2 x : Y) z.1.
have hd : continuous d.
  move=> z; exact: continuous_comp (hF z) (@metric_pair_distance_continuous R Y (F z)).
pose W := d @^-1` [set r : real_line_metric R | mdist (0:real_line_metric R) r<e].
have hW : open W.
  apply: open_comp (@metric_open_ball_open R [the metricType R of real_line_metric R]
    (0:real_line_metric R) e)=> z _.
  exact: hd.
have hWy : W (y,p).
  have hy : y=euclidean_projection_linear p x := hxy.
  change (is_true (mdist (0:real_line_metric R) (d (y,p))<e)).
  rewrite /d /= hy !mdistxx; exact he.
have hnb : nbhs (y,p) W by rewrite openE in hW; exact: hW _ hWy.
apply: (@filterS _ (nbhs (y,p)) _ W _ _ hnb)=> z hz.
have hz' : mdist (euclidean_projection_linear z.2 x : Y) z.1<e.
  change (is_true (mdist (0:real_line_metric R) (d z)<e)) in hz.
  by rewrite real_line_metric_distanceE sub0r normrN (ger0_norm (mdist_ge0 _ _)) in hz.
have [u [hu hdist]] := @orthogonal_projection_exact_distance_lift R n m z.2 x z.1.
exists u; split.
- apply: hball; change (is_true (mdist x u<e)); by rewrite hdist.
- exact: esym hu.
Qed.
