(** Federer (1969), 3.3.20, pp. 307–308:
    local existence and injection of actual original interval similarities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge AffineIntervalTransportUP
  PositiveAffineClosedSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_interval_transport_exists]: supporting
    actual similarity reduction in 3.3.20,
    pp. 307–308. Every original compact interval
    has a compact interval image with the stated
    exact laws. The selected auxiliary map remains
    existential and is not an exposed construction. *)
Theorem affine_interval_transport_exists (R:realType) (a r:R):
  0<r ->exists M,is_affine_interval_transport a r M.
Proof.
move=>hr.
have hEach (S:compact_real_intervals R):exists T:compact_real_intervals R,
    val T=(fun x:R=>a+r * x) @` val S.
  have [l [h [hlh hS]]]:=set_valP S.
  have hValue:(fun x:R=>a+r * x) @` val S=(`[a+r * l,a+r * h]:set (real_line_metric R)).
    by rewrite hS positive_affine_closed_segment_image.
  have hOrder:a+r * l<=a+r * h by rewrite lerD2l ler_pM2l.
  have hInterval:is_compact_real_interval ((fun x:R=>a+r * x) @` val S).
    exists (a+r * l),(a+r * h);by split.
  exists (Sub ((fun x:R=>a+r * x) @` val S) (mem_set hInterval));by [].
have [M hM]:=choice hEach.
by exists M.
Qed.

(** Source for [affine_interval_transport_injective]: supporting
    distinct original interval images under positive
    similarities, 3.3.20, pp. 307–308.
    Actual scalar cancellation and the independent
    set-image laws prove injection. *)
Lemma affine_interval_transport_injective (R:realType) (a r:R) M:
  0<r ->is_affine_interval_transport a r M ->injective M.
Proof.
move=>hr hM S T hEqual.
have hNZ:r!=0 by rewrite gt_eqF.
have hInjective:injective (fun x:R=>a+r * x).
  move=>x y h;apply:(mulfI hNZ);exact:(addrI a h).
have hImage:(fun x:R=>a+r * x) @` val S=(fun x:R=>a+r * x) @` val T.
  by rewrite -(hM S) -(hM T) hEqual.
apply:val_inj;apply/seteqP;split=>x hx.
- have hMember:((fun x:R=>a+r * x) @` val T) (a+r * x) by rewrite -hImage;exists x.
  have [y hy hValue]:=hMember.
  have hyx:y=x:=hInjective _ _ hValue.
  by rewrite -hyx.
- have hMember:((fun x:R=>a+r * x) @` val S) (a+r * x) by rewrite hImage;exists x.
  have [y hy hValue]:=hMember.
  have hyx:y=x:=hInjective _ _ hValue.
  by rewrite -hyx.
Qed.
