(** Federer (1969), 3.3.19, p. 304:
    the elementary pair-distance inequality in the
    original cyclic retraction argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [retraction_pair_weight_budget]: the
    third and fourth lines of the cyclic inequality
    in 3.3.19, p. 304, for two
    actual selected points. Two metric triangles,
    nonexpansion and the original local endpoint
    bounds pay both actual weights. *)
Lemma retraction_pair_weight_budget (R:realType) (X:metricType R)
    (P:X->X) (c d x y:X) (b u v:R):
  2*b<=mdist c d ->u<=b-mdist (P x) c ->v<=b-mdist (P y) d ->
  mdist (P x) (P y)<=mdist x y ->u+v<=mdist x y.
Proof.
move=>hSeparation hX hY hContraction.
have hTriangle1:=metric_triangle c (P x) d.
have hTriangle2:=metric_triangle (P x) (P y) d.
rewrite (metric_sym c (P x)) in hTriangle1;lra.
Qed.
