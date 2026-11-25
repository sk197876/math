(** Federer (1969), 4.1.7, p. 359: the
    pushforward requires properness only on the
    actual current support. The compact preimage
    below is precisely the set to be
    enclosed by the original scalar cutoff. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentSupportGeometry CurrentDomain
  SmoothCompactSet ProperMapUP IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentProperSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n q m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R q).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R q)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable V:set Y.
Variable T:@current_space R h2 n U hU m.
Local Notation support := (@current_support R h2 n U hU m T).
Local Notation ST := [the topologicalType of set_type (support:set XT)].
Local Notation VT := (current_domain R q V).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.

(** Source for [current_map_on_support]: the
    literal restriction f|spt T with its
    target in V, supporting Federer 4.1.7,
    p. 359. Its carrier is exactly
    the original support, without enlarging it. *)
Definition current_map_on_support:ST->VT:=
  fun x=>exist _ (f (set_val x)) (mem_set (hImage (set_val x) (set_valP x).1)).

(** Source for [is_current_proper_on_support]: the
    original properness hypothesis on f|spt T,
    Federer 4.1.7, p. 359, using
    the existing topological definition of properness. *)
Definition is_current_proper_on_support:Prop:=is_proper_map current_map_on_support.

(** Source for [current_proper_support_compact_preimage]:
    spt T intersected with f inverse(K)
    is a compact subset of U for
    compact K in V, supporting the
    defining cutoff of Federer 4.1.7,
    p. 359. Global properness of f
    is not assumed. *)
Theorem current_proper_support_compact_preimage (K:smooth_compact_set hNY V):
  is_current_proper_on_support ->
  @compact XT [set x|support x /\smooth_compact_carrier K (f x)].
Proof.
move=>hProper.
have hK:@compact VT (set_val @^-1` smooth_compact_carrier K).
  exact:(@set_type_compact_preimage YT V (smooth_compact_carrier K)
    (smooth_compact_is_compact K) (smooth_compact_in_domain K)).
have hPre:=hProper (set_val @^-1` smooth_compact_carrier K) hK.
have hCompact:@compact XT (set_val @` (current_map_on_support @^-1`
    (set_val @^-1` smooth_compact_carrier K))).
  apply:continuous_compact hPre;apply:continuous_subspaceT=>x;exact:set_type_val_continuous.
have hEq:set_val @` (current_map_on_support @^-1` (set_val @^-1` smooth_compact_carrier K))=
    [set x:XT|support x /\smooth_compact_carrier K (f x)].
  apply:funext=>x;apply:propext;split.
  - move=>[y hy <-];split;first exact:set_valP y.
    exact:hy.
  - move=>[hx hKx];exists (exist _ x (mem_set hx));by [].
by rewrite hEq in hCompact.
Qed.

(** Source for [current_proper_support_compact_locus]:
    the original preimage locus as an
    actual compact subset of U, supporting
    the scalar cutoff in Federer 4.1.7,
    p. 359. This record retains the
    exact set, rather than choosing a larger
    preimage or a globally proper map. *)
Definition current_proper_support_compact_locus
    (hProper:is_current_proper_on_support) (K:smooth_compact_set hNY V):smooth_compact_set hNX U:=
  @Build_smooth_compact_set R X NX hNX U
    [set x|support x /\smooth_compact_carrier K (f x)]
    (fun x hx=>hx.1.1) (@current_proper_support_compact_preimage K hProper).
End CurrentProperSupport.
