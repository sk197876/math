(** Federer (1969), 4.1.14, p. 371: the original
    composition g composed with f is locally Lipschitz.
    The supporting local distance argument uses only
    2.2.7, p. 64, on the original relative domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import LipschitzUP LipschitzBasic MetricLipschitzComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_local_lipschitz_composition]: the
    local Lipschitz class of 2.2.7, p. 64, is
    closed under the original composition of 4.1.14,
    p. 371. Only f(A) contained in B is required;
    neither relative domain is required to be open. *)
Theorem metric_local_lipschitz_composition (R : realType)
    (X Y Z : metricType R) (A : set X) (B : set Y)
    (f : X -> Y) (g : Y -> Z) :
  (forall x, A x -> B (f x)) ->
  @is_locally_metric_lipschitz R X Y A f ->
  @is_locally_metric_lipschitz R Y Z B g ->
  @is_locally_metric_lipschitz R X Z A (fun x => g (f x)).
Proof.
move=> hImage hF hG x hx.
have [WF [hWF [L [hL hFL]]]] := hF x hx.
have [WG [hWG [M [hM hGM]]]] := hG (f x) (hImage x hx).
have [e he hBall] := (metricType_numDomainType.nbhs_mdistP (f x) WG).1 hWG.
have hRadius : 0<e/L by rewrite divr_gt0.
pose W := WF `&` ball x (e/L).
have hW : nbhs x W := filterI hWF (nbhsx_ballx x (e/L) hRadius).
have hXWF : WF x := nbhs_singleton hWF.
have hIntermediate : forall y, (A `&` W) y -> (B `&` WG) (f y).
  move=> y [hy [hyWF hyBall]]; split; first exact: hImage y hy.
  apply: hBall.
  have hNear : mdist x y<e/L by move: hyBall; rewrite ballEmdist.
  have hBound := hFL.2 x y (conj hx hXWF) (conj hy hyWF).
  apply: (le_lt_trans hBound).
  by rewrite mulrC -ltr_pdivlMr.
have hRestricted : @is_metric_lipschitz_bound R X Y (A `&` W) f L.
  apply: (@metric_lipschitz_bound_restrict R X Y (A `&` WF)
    (A `&` W) f L _ hFL).
  move=> y [hy [hyWF _]]; exact: conj hy hyWF.
exists W; split; first exact: hW.
exists (M*L); split; first exact: mulr_gt0 hM hL.
exact: (@metric_lipschitz_composition_bound R X Y Z
  (A `&` W) (B `&` WG) f g L M hIntermediate hRestricted hGM).
Qed.
