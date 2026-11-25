(** Federer (1969), 4.1.8, p. 362: the original
    affine segment on its actual compact parameter domain.
    The domain condition says exactly that A contains
    the original closed segment. Existence and continuity
    are proved separately from the value specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology normedtype.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentDomain CurrentSegmentParameter ConvexMetricSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Section CurrentSegmentMapUP.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Variable A:set X.
Variables u v:X.
Local Notation Q := (current_segment_parameter R).
Local Notation AT := (current_domain R n A).

(** Source for [is_current_segment_domain]: A contains the
    line segment with endpoints u and v, the original
    hypothesis in Federer 4.1.8, p. 362. No convexity
    of the whole domain is required. *)
Definition is_current_segment_domain:Prop:=
  forall t:R,t \in `[0,1]->A (metric_segment_point u v t).

(** Source for [current_segment_point_original_formula]: the
    original segment point a+t(b-a) equals the printed
    (1-t)a+tb, supporting Federer 4.1.8, p. 362. *)
Lemma current_segment_point_original_formula t:
  metric_segment_point u v t=(1-t)*:u+t*:v.
Proof. by rewrite /metric_segment_point scalerBr scalerBl scale1r addrA addrAC. Qed.

(** Source for [is_current_segment_map]: the actual-domain
    segment map has precisely the original affine values,
    supporting Federer 4.1.8, p. 362. Neither continuity
    nor any current or boundary identity is assumed. *)
Definition is_current_segment_map (f:Q->AT):Prop:=
  forall t:Q,set_val (f t)= metric_segment_point u v (set_val t).

(** Source for [current_segment_map_exists]: the original
    segment has an actual map into A under its original
    containment hypothesis, supporting Federer 4.1.8,
    p. 362. The subtype map is only an existence witness. *)
Theorem current_segment_map_exists:is_current_segment_domain ->exists f:Q->AT,is_current_segment_map f.
Proof.
move=>hSegment.
exists (fun t:Q=>exist _ (metric_segment_point u v (set_val t))
  (mem_set (@hSegment (set_val t) (set_valP t)))).
by [].
Qed.

(** Source for [current_segment_map_unique]: the original
    affine values determine the actual-domain map uniquely,
    supporting Federer 4.1.8, p. 362. *)
Theorem current_segment_map_unique (f g:Q->AT):
  is_current_segment_map f ->is_current_segment_map g ->f= g.
Proof.
move=>hF hG;apply:funext=>t;apply:val_inj.
change (set_val (f t)=set_val (g t)).
by rewrite (hF t) (hG t).
Qed.
End CurrentSegmentMapUP.
