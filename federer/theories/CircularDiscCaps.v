(** Federer (1969), 3.3.19, p. 305: the literal
    circular caps S(z,r,u,gamma) used in the actual
    conical-density comparison. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP Bilinear InnerNorm
  InnerNormInequalities InnerMetric InnerCoordinateContinuity OrthonormalFamilies MetricClosedBalls
  RealTrigonometryUP CircularTrigonometryUP CircularTrigonometrySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Caps.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [circular_disc_cap]: the exact original
    B(z,r) intersect {x:(x-z).u>=r cos(gamma)} in
    3.3.19, p. 305. No replacement cap or
    selected angular coordinate is used. *)
Definition circular_disc_cap (z:E) (r:R) (u:E) (gamma:R):set E:=
  metric_closed_ball z r `&` [set x:E|r* C gamma<=B (x-z) u].

(** Source for [circular_disc_cap_closed]: the original
    caps in 3.3.19, p. 305, are closed. Actual
    coordinate continuity proves the halfspace condition. *)
Lemma circular_disc_cap_closed (z:E) (r:R) (u:E) (gamma:R):
  closed (circular_disc_cap z r u gamma).
Proof.
apply:closedI;first exact:metric_closed_ball_closed.
have hEqual:[set x:E|r* C gamma<=B (x-z) u]=
    [set x:E|r* C gamma+B z u<=inner_coordinate hE u x].
  have hLinear x:B (x-z) u=B x u-B z u:=bilBl (inner_bilinear hE) x z u.
  apply/seteqP;split=>x hx.
  - change (is_true (r*C gamma+B z u<=inner_coordinate hE u x)).
    change (is_true (r*C gamma<=B (x-z) u)) in hx.
    rewrite hLinear in hx;rewrite inner_coordinateE;lra.
  - change (is_true (r*C gamma<=B (x-z) u)).
    change (is_true (r*C gamma+B z u<=inner_coordinate hE u x)) in hx.
    rewrite inner_coordinateE in hx;rewrite hLinear;lra.
rewrite hEqual.
change (closed ((fun x:E=>(inner_coordinate hE u x:R^o)) @^-1`
  [set t:R^o|r* C gamma+B z u<=t])).
apply:preimage_closed;last exact:closed_ge.
by move=>x _;exact:inner_coordinate_continuous.
Qed.

(** Source for [circular_disc_cap_pi]: at the full
    half-angle pi the original cap is the whole original
    closed disc, retaining the endpoint allowed by
    3.3.19, p. 305. Zero radius is also retained. *)
Lemma circular_disc_cap_pi (z u:E) (r:R):
  0<=r ->inner_norm hE u= 1 ->
  circular_disc_cap z r u p= metric_closed_ball z r.
Proof.
move=>hr hu;apply/seteqP;split;first by move=>x [hx _].
move=>x hx;split=>//.
have hCauchy:= inner_cauchy hE (x-z) u.
rewrite hu mulr1 -inner_metric_distanceE (metric_sym x z) in hCauchy.
have hxReal:mdist z x<=r:= hx.
have hAbsolute:`|B (x-z) u|<=r:= le_trans hCauchy hxReal.
have /andP[hLower hUpper]:(-r<=B (x-z) u<=r) by rewrite -ler_norml.
by rewrite (circular_trig_cosine_pi (@CircularTrigonometry.laws R)) mulrN1.
Qed.
End Caps.
