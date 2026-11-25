(** Federer (1969), 4.1.2, p. 347: local Lipschitz
    bounds give a single finite bound on every compact source
    part. Compact image bounds and the registered metric finite-cover
    argument supply the control needed for input localization. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormClassZeroWhole NormCompactFunctionBound
  LipschitzUP LipschitzBasic MetricCompactLocalLipschitz MetricLocalLipschitzContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_local_lipschitz_compact]: the compact Lipschitz
    control used for the locally Lipschitz input in Federer 4.1.2,
    p. 347. No convexity of the compact set or finite-dimensional
    assumption on the target is imposed. *)
Theorem norm_local_lipschitz_compact (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (f:X->Y) (K:set (real_norm_metric_space hNX)):
  is_locally_metric_lipschitz setT
    (f:real_norm_metric_space hNX->real_norm_metric_space hNY) ->
  compact K ->is_metric_lipschitz K
    (f:real_norm_metric_space hNX->real_norm_metric_space hNY).
Proof.
move=>hLocal hK.
have hCont:=metric_local_lipschitz_continuous_whole hLocal.
have[M [hM hBound]]:=@norm_class_zero_compact_bounded R X Y NX NY hNX hNY
  setT K f hK (fun _ _=>Logic.I) (norm_continuous_whole_class_zero hCont).
apply:(@metric_compact_local_lipschitz R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) K f (M+M) hK (addr_ge0 (ltW hM) (ltW hM))).
- move=>x y hx hy.
  change (is_true (NY (f x-f y)<=M+M)).
  have h:=real_seminorm_triangle hNY.1 (f x) (-f y).
  rewrite (real_seminorm_negate hNY.1) in h.
  exact:le_trans h (lerD (hBound x hx) (hBound y hy)).
- move=>x hx.
  have[V [hV [L [hL hLip]]]]:=hLocal x Logic.I.
  have[r hr hBall]:=(metricType_numDomainType.nbhs_mdistP x V).1 hV.
  exists r,L; split; first exact hr.
  apply:(@metric_lipschitz_bound_restrict R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) (setT `&` V)
    [set y|mdist x y<r] f L _ hLip).
  move=>y hy; split; first exact Logic.I; exact:hBall y hy.
Qed.
