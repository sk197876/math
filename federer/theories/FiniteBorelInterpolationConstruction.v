(** Federer (1969), 2.2.15, p. 71, final criterion: private finite
    interpolation witness. Code the finite target set injectively by natural
    numbers, viewed as real inputs, and use a fixed target value elsewhere. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground FiniteExceptionalBorel FiniteBorelInterpolationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_borel_interpolation_exists]: supporting
    existence for the necessity of Federer 2.2.15, p. 71.
    The nonempty-target hypothesis supplies the value away from
    the finitely many interpolation inputs, including when Z is empty. *)
Theorem finite_borel_interpolation_exists (R : realType) (Y : topologicalType)
    (Z : set Y) (y0 : Y) : finite_set Z ->
  exists f : real_line_metric R -> Y, exists F,
    is_finite_borel_interpolation Z f F.
Proof.
move=> hZ.
have /countable_injP[g hg] := finite_set_countable hZ.
pose code (y : Y) : real_line_metric R := (g y)%:R.
have hinj x y : Z x -> Z y -> code x = code y -> x = y.
  move=> hx hy he; apply: hg; [by rewrite inE|by rewrite inE|].
  apply/eqP; rewrite -(@eqr_nat R); apply/eqP; exact he.
pose P x y := Z y /\ code y = x.
pose f (x : real_line_metric R) :=
  if pselect (exists y, P x y) is left h then projT1 (cid h) else y0.
have hval y : Z y -> f (code y) = y.
  move=> hy; rewrite /f; case: pselect=> [h|h].
  - have [hz he] := projT2 (cid h); exact: hinj hz hy he.
  - exfalso; apply: h; exists y; by split.
have hoff x : ~ (code @` Z) x -> f x = y0.
  move=> hx; rewrite /f; case: pselect=> [h|h] //.
  exfalso; apply: hx; have [y [hy he]] := h; by exists y.
exists f, (code @` Z); constructor.
- exact: finite_image code hZ.
- exact: finite_exceptional_map_borel (finite_image code hZ) hoff.
- move=> y hy; exists (code y); first by exists y.
  exact: hval hy.
Qed.
