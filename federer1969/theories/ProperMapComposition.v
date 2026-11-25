(** Federer (1969), 4.1.7, p. 359: composition
    of current pushforwards assumes only that
    g composed with f is proper on
    the original support. These general-topology
    consequences derive the needed separate proper
    restrictions from that hypothesis. *)
From mathcomp Require Import all_boot boolp functions classical_sets topology.
From Federer Require Import ProperMapUP IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [proper_map_composition]: inverse images
    under a composite preserve compactness when
    both maps are proper, supporting Federer
    4.1.7, p. 359, by the definition
    of 2.2.17, p. 72. *)
Theorem proper_map_composition (X Y Z:topologicalType) (f:X->Y) (g:Y->Z):
  is_proper_map f->is_proper_map g->is_proper_map (g \o f).
Proof. move=>hF hG K hK;exact:hF (g @^-1` K) (hG K hK). Qed.

(** Source for [proper_composite_first]: if g
    composed with f is proper, then
    f is proper when both maps are
    continuous and the intermediate space is
    Hausdorff, supporting Federer 4.1.7,
    p. 359. No properness of g
    on its whole domain is assumed. *)
Theorem proper_composite_first (X Y Z:topologicalType) (f:X->Y) (g:Y->Z):
  hausdorff_space Y->continuous f->continuous g->is_proper_map (g \o f)->is_proper_map f.
Proof.
move=>hY hF hG hComposite K hK.
have hImage:compact (g @` K).
  apply:continuous_compact hK;exact:continuous_subspaceT hG.
have hClosed:closed (f @^-1` K).
  apply:preimage_closed (compact_closed hY hK)=>x _;exact:hF.
apply:(@subclosed_compact X (f @^-1` K) ((g \o f) @^-1` (g @` K))
  hClosed (hComposite (g @` K) hImage))=>x hx.
by exists (f x).
Qed.

(** Source for [proper_composite_on_image]: g is
    proper on f(X) when g composed
    with f is proper and f is
    continuous, supporting the original pushforward
    composition in Federer 4.1.7, p. 359.
    The image has its actual relative topology. *)
Theorem proper_composite_on_image (X Y Z:topologicalType) (f:X->Y) (g:Y->Z):
  continuous f->is_proper_map (g \o f)->
    is_proper_map (fun y:set_type (f @` setT)=>g (set_val y)).
Proof.
move=>hF hComposite K hK.
pose A:=f @` ((g \o f) @^-1` K).
have hA:compact A.
  apply:continuous_compact (hComposite K hK);exact:continuous_subspaceT hF.
have hImage:A `<=` (f @` setT) by move=>y [x hx <-];by exists x.
have hEq:((fun y:set_type (f @` setT)=>g (set_val y)) @^-1` K)=
    (set_val @^-1` A:set (set_type (f @` setT))).
  apply:funext=>y;apply:propext;split.
  - move=>hy;have[x _ hxy]:=set_valP y.
    exists x;last exact:hxy.
    change (K (g (f x)));by rewrite hxy.
  - move=>[x hx hxy];change (K (g (set_val y)));by rewrite -hxy.
rewrite hEq;exact:(@set_type_compact_preimage Y (f @` setT) A hA hImage).
Qed.

(** Source for [proper_map_closed_restriction]: restricting
    a proper map to a closed subset
    preserves properness, supporting boundary and
    image-support restrictions in Federer 4.1.7,
    p. 359. The earlier subspace-inclusion
    theorem supplies the proof. *)
Theorem proper_map_closed_restriction (X Y:topologicalType) (f:X->Y) (S:set X):
  closed S->is_proper_map f->is_proper_map (fun x:set_type S=>f (set_val x)).
Proof.
move=>hS hF.
exact:(@proper_map_composition (set_type S) X Y set_val f
  (@set_type_val_proper X S hS) hF).
Qed.
