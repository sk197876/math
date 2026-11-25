(** Federer (1969), 3.2.22, pp. 258–259: the
    coordinate composites are Lipschitz by the distance
    definition of 2.2.7, pp. 63–64. The supporting
    bounds retain the actual relative domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_lipschitz_composition_bound]: supporting
    Lipschitz coordinate composites in Federer 3.2.22,
    p. 259, from 2.2.7, pp. 63–64.
    Multiply the two distance bounds, requiring only
    that the actual first image lies in the second domain. *)
Lemma metric_lipschitz_composition_bound (R:realType) (X Y Z:metricType R)
    (A:set X) (B:set Y) (f:X->Y) (g:Y->Z) (L M:R):
  (forall x,A x ->B (f x)) ->
  is_metric_lipschitz_bound A f L ->is_metric_lipschitz_bound B g M ->
  is_metric_lipschitz_bound A (fun x=>g (f x)) (M*L).
Proof.
move=>hImage hF hG; split; first exact:(mulr_ge0 hG.1 hF.1).
move=>x y hx hy.
apply:(le_trans (hG.2 (f x) (f y) (hImage x hx) (hImage y hy)) _).
rewrite -mulrA; exact:(ler_wpM2l hG.1 (hF.2 x y hx hy)).
Qed.

(** Source for [metric_lipschitz_whole_composite]: existence
    of a finite Lipschitz bound for F composed psi_i
    and G_j composed F composed psi_i in Federer
    3.2.22, p. 259. Zero optimal bounds remain
    allowed because the definition witnesses any positive bound. *)
Lemma metric_lipschitz_whole_composite (R:realType) (X Y Z:metricType R)
    (f:X->Y) (g:Y->Z):
  is_metric_lipschitz setT f ->is_metric_lipschitz setT g ->
  is_metric_lipschitz setT (fun x=>g (f x)).
Proof.
move=>[L [hL hF]] [M [hM hG]]; exists (M*L); split; first exact:mulr_gt0 hM hL.
exact:(metric_lipschitz_composition_bound (fun _ _=>Logic.I) hF hG).
Qed.
