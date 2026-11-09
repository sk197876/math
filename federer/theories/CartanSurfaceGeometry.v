(** Federer (1969), 3.4.5, p. 321, citing Cartan
    (1957), p. 97: near the flat endpoint the actual
    cubic surface is just its axis. It is a proper
    set, although all its global analytic equations will vanish. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra ring.
From Federer Require Import GrassmannAbbreviations FlatExponentialUP FlatExponentialSealed FlatExponentialOrder
  CartanSurfaceUP CartanSurfaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cartan_cubic_near_flat_axis]: the elementary
    axis-neighbourhood estimate on Cartan p. 97, cited in
    3.4.5, p. 321. The scalar proof retains actual
    positive z and the exact bound 0<=a<= 1. *)
Lemma cartan_cubic_near_flat_axis (R:realType) (x y z a:R):
  0<=a ->a<= 1 ->1/2<z ->`|x|<1/2 ->
  (z*(x^+2+y^+2)=x^+3*a <->x=0 /\ y=0).
Proof.
move=>ha haOne hz hx;split;last by move=>[-> ->];ring.
move=>hEquation.
have hx2:0<=x^+2:=sqr_ge0 x.
have hy2:0<=y^+2:=sqr_ge0 y.
have hZ:0<z by lra.
have hAbs:0<=`|x| := normr_ge0 x.
have hCube:x^+3*a<=`|x|*x^+2.
  have hLe:x<=`|x| := ler_norm x.
  have hxa:x*a<=`|x|.
    apply:le_trans (ler_wpM2r ha hLe) _.
    have hh:=ler_wpM2l hAbs haOne;by rewrite mulr1 in hh.
  have hh:=ler_wpM2r hx2 hxa.
  have hEqual:x^+3*a=(x*a)*x^+2 by rewrite !exprS expr0;ring.
  by rewrite hEqual.
have hZeroX:x^+2=0 by nra.
have hZeroY:y^+2=0 by nra.
split;apply/eqP;[move/eqP:hZeroX|move/eqP:hZeroY];by rewrite sqrf_eq0.
Qed.

(** Source for [cartan_surface_near_flat_axis]: the actual
    surface equals the axis on the specified neighbourhood,
    supporting local analyticity at the flat endpoint in
    the example cited at 3.4.5, p. 321. *)
Lemma cartan_surface_near_flat_axis (R:realType) (v:R_n R 3):
  1/2<v ord_max ->`|v ord0|<1/2 ->
  (CartanSurface.set v <->v ord0=0 /\v (Ordinal (isT:(1<3)%N))=0).
Proof.
move=>hz hx;rewrite (cartan_surface_membership (@CartanSurface.laws R)).
exact:(@cartan_cubic_near_flat_axis R (v ord0) (v (Ordinal (isT:(1<3)%N))) (v ord_max)
  (FlatExponential.value (1-v ord_max))
  (@flat_exponential_nonnegative R (1-v ord_max))
  (@flat_exponential_unit_bound R (1-v ord_max)) hz hx).
Qed.

(** Source for [cartan_surface_contains_axis]: the whole
    original z-axis lies in the actual cubic surface,
    Cartan p. 97, cited in 3.4.5, p. 321. *)
Lemma cartan_surface_contains_axis (R:realType) (v:R_n R 3):
  v ord0=0 ->v (Ordinal (isT:(1<3)%N))=0 ->CartanSurface.set v.
Proof.
move=>hx hy;apply/(cartan_surface_membership (@CartanSurface.laws R)).
rewrite hx hy;ring.
Qed.

(** Source for [cartan_surface_is_proper]: the point (1,0,1)
    is outside the original cubic surface, so non-globality
    cannot follow from using the whole space, 3.4.5, p. 321. *)
Lemma cartan_surface_is_proper (R:realType):
  exists v:R_n R 3,~CartanSurface.set v.
Proof.
exists [ffun i:'I_3=>if i==Ordinal (isT:(1<3)%N) then 0 else 1].
move/(cartan_surface_membership (@CartanSurface.laws R)).
rewrite !ffunE /= subrr (flat_exponential_nonpositive_value (@FlatExponential.laws R) (lexx 0)).
rewrite !expr1n expr0n addr0 mulr0 mulr1=>hOne.
by move/eqP:hOne;rewrite oner_eq0.
Qed.

(** Source for [cartan_surface_flat_plane]: on the actual
    flat plane the original surface consists exactly of its
    axis point, supporting the example cited at 3.4.5, p. 321. *)
Lemma cartan_surface_flat_plane (R:realType) (v:R_n R 3):
  v ord_max= 1 ->(CartanSurface.set v <->v ord0=0 /\v (Ordinal (isT:(1<3)%N))=0).
Proof.
move=>hz;rewrite (cartan_surface_membership (@CartanSurface.laws R)) hz subrr
  (flat_exponential_nonpositive_value (@FlatExponential.laws R) (lexx 0)) mulr0 mul1r.
split;last by move=>[-> ->];ring.
move=>hZero.
have hx:=sqr_ge0 (v ord0).
have hy:=sqr_ge0 (v (Ordinal (isT:(1<3)%N))).
have hxZero:(v ord0)^+2=0 by nra.
have hyZero:(v (Ordinal (isT:(1<3)%N)))^+2=0 by nra.
split;apply/eqP;[move/eqP:hxZero|move/eqP:hyZero];by rewrite sqrf_eq0.
Qed.
