(** Federer (1969), 3.3.20, p. 307: critical and supercritical overlap slopes. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealPower BinaryCantorRatioBounds CriticalProjectionScalarBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_binary_projection_overlap_slope]: at m=1/2
    the printed overlap interval reduces to slope one half, 3.3.20,
    p. 307. The original division-free equations retain all endpoints. *)
Lemma critical_binary_projection_overlap_slope (R:realType) (u v:R):
  ((1-2 * (1/4:R)) * u<=v /\(1-2 * (1/4:R)) * v<=(1/4:R) * u)
    <->v=u/2.
Proof. split=>[[h0 h1]|h];lra. Qed.

(** Source for [supercritical_binary_projection_strict_overlap]: for
    every original m>1/2, the actual slope-one-half unit direction
    lies strictly inside both overlap inequalities and the ordered
    positive quadrant, 3.3.20, p. 307. This proves a local interior
    witness before the original parameter-space open-set argument. *)
Theorem supercritical_binary_projection_strict_overlap (R:realType) (m:R):
  1/2<m ->m<1 ->
  let s:=real_power 2 (-m^-1) in
  let u:=(2:R)/Num.sqrt 5 in let v:=(1:R)/Num.sqrt 5 in
  u^+2+v^+2= 1 /\0<v /\v<u /\(1-2 * s) * u<v /\(1-2 * s) * v<s * u.
Proof.
move=>hSuper hm1 s u v.
have hm:0<m by lra.
have [hBounds hStrict]:=binary_cantor_original_ratio_bounds hm hm1.
have hsQuarter:1/4<s:=hStrict hSuper.
have [hv [hvu [hUnit [hRatio _]]]]:=@critical_projection_extremal_direction R.
change (is_true (0<v)) in hv.
change (v=u/2) in hRatio.
change (u^+2+v^+2= 1) in hUnit.
have hu:0<u by lra.
have hVU:v<u by lra.
have hMiddle:(1-2 * s) * u<v by nra.
have hSide:(1-2 * s) * v<s * u by nra.
exact:(conj hUnit (conj hv (conj hVU (conj hMiddle hSide)))).
Qed.
