(** Federer (1969), 4.1.7, p. 359:
    the original half-line inclusion is Lipschitz
    but is not proper on the
    current's support (0,b]. The support is
    not compact in U, despite finite
    normal mass. Compact positive coordinate bounds
    prove this without a new measure construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate EuclideanOneNormDifferential
  CurrentDomain CurrentSpaces CurrentSupportGeometry CurrentProperSupport CurrentProperSupportDomain
  HalflineCurrents HalflineCurrentSupport HalflineFiniteNormalMass NormalCurrentsUP CurrentNormalMass
  CompactPositiveScalarBounds MetricSubsetBackground MetricClosedBalls EuclideanNormClosedBalls SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflineCurrentTopology.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation U := (@current_halfline_domain R).
Local Notation hU := (@current_halfline_domain_open R).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation hImage := (fun (x:X) (_:U x)=>Logic.I).
Local Notation UM := (metric_subset (U:set XT)).
Local Notation FM := (metric_subset (Full:set XT)).
Local Notation inclusion := (@current_map_on_domain R 1 1 U Full id hImage).
Variable b:R.
Hypothesis hb:0<b.
Local Notation T := (@halfline_current R h2 b).
Local Notation support := (@current_support R h2 1 U hU 1%N T).

(** Source for [halfline_current_support_not_compact]:
    the original support (0,b] is not
    compact in the source U, supporting
    the properness obstruction in Federer 4.1.7,
    p. 359. A compact support would
    have a positive minimum coordinate, contradicted
    by its points arbitrarily close to zero. *)
Theorem halfline_current_support_not_compact:~@compact XT support.
Proof.
move=>hCompact.
have hNonempty:support !=set0.
  exists (euclidean_one_embed b);exact:(@halfline_current_support_endpoint R h2 b hb).
have hCoordinate:continuous (fun x:XT=>(x ord0:R^o)).
  exact:(@halfline_support_coordinate_continuous R).
have [a [z [ha [hz [hA hBounds]]]]]:=@compact_positive_scalar_bounds R XT support
  (fun x=>(x ord0:R^o)) hNonempty hCompact hCoordinate (fun x hx=>hx.1).
pose q:=Num.min (a ord0/2) (b/2).
have hQ:0<q by rewrite /q lt_min !divr_gt0 ?ltr0n.
have hQa:q<=a ord0/2 by rewrite /q ge_min lexx.
have hQb:q<=b/2 by rewrite /q ge_min lexx orbT.
have hQB:q<=b by lra.
have hSupport:support (euclidean_one_embed q).
  rewrite (@halfline_current_support_exact R h2 b hb).
  change (is_true (0<euclidean_one_project (euclidean_one_embed q)<=b)).
  rewrite euclidean_one_embedK;by apply/andP;split.
have hLower: a ord0<=q.
  have h:=(andP (hBounds (euclidean_one_embed q) hSupport)).1.
  change (is_true (a ord0<=euclidean_one_project (euclidean_one_embed q))) in h.
  by rewrite euclidean_one_embedK in h.
have hHalf:a ord0/2<a ord0 by lra.
have hFalse:=le_lt_trans (le_trans hLower hQa) hHalf.
by rewrite ltxx in hFalse.
Qed.

(** Source for [halfline_current_not_normal]:
    the original example has finite normal
    mass and is locally normal but
    is not normal, supporting Federer
    4.1.7, p. 359, with the
    normality definition on p. 358. *)
Theorem halfline_current_not_normal:~@is_normal_current R h2 1 U hU 1%N T.
Proof. move=>hNormal;exact:(halfline_current_support_not_compact hNormal.2). Qed.

(** Source for [halfline_inclusion_lipschitz]: the
    original inclusion U into R has
    Lipschitz bound one in the actual
    relative Euclidean metrics, Federer 4.1.7,
    p. 359. This estimate does not
    imply the required support-properness. *)
Theorem halfline_inclusion_lipschitz (x y:UM):
  @mdist R FM (inclusion x) (inclusion y)<=1*@mdist R UM x y.
Proof.
change (is_true (NX (set_val x-set_val y)<=1*NX (set_val x-set_val y))).
by rewrite mul1r.
Qed.

(** Source for [halfline_inclusion_not_proper]: the
    original inclusion fails to be proper
    on spt T=(0,b], establishing the
    missing hypothesis in Federer 4.1.7,
    p. 359. A compact whole-line ball
    has the entire noncompact support as
    its inverse-image locus. *)
Theorem halfline_inclusion_not_proper:
  ~@is_current_proper_on_support R h2 1 1 1%N U hU Full T id hImage.
Proof.
move=>hProper.
pose B:=@metric_closed_ball R XT 0 b.
have hCompact:@compact XT B:=@euclidean_norm_closed_ball_compact R 1 0 b.
pose K:=@Build_smooth_compact_set R X NX hNX Full B (fun _ _=>Logic.I) hCompact.
have hSupportBall:support `<=` B.
  move=>x hx.
  have /andP [hx0 hxb]:=(@halfline_current_support_upper R h2 b x hx).
  change (is_true (NX (0-x)<=b)).
  by rewrite sub0r (real_seminorm_negate hNX.1) euclidean_one_norm_coordinate (ger0_norm (ltW hx0)).
have hPre:=@current_proper_support_compact_preimage R h2 1 1 1%N U hU Full T id hImage K hProper.
change (@compact XT [set x|support x /\B x]) in hPre.
have hEqual:[set x:XT|support x /\B x]=support.
  apply/seteqP;split;first by move=>x hx;exact:hx.1.
  move=>x hx;exact:conj hx (hSupportBall x hx).
rewrite hEqual in hPre;exact:(halfline_current_support_not_compact hPre).
Qed.
End HalflineCurrentTopology.
