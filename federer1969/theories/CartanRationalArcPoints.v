(** Federer (1969), 3.4.5, p. 321: actual
    real arcs on the adapted cubic surface, supporting
    the real Taylor proof of the local/global example
    cited to Cartan (1957), pp. 97–99. These arcs
    avoid a complex-continuation premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import GrassmannAbbreviations FlatExponentialSealed FlatExponentialOrder
  CartanSurfaceUP CartanSurfaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cartan_rational_arc_points_exist]: the
    actual rational arc with x=z(1+t^2)/a(z), y=t*x,
    joining the origin with the regular part of the
    original cubic surface. This supports the example cited
    in 3.4.5, p. 321. Every z<1 is
    retained, including z=0. *)
Theorem cartan_rational_arc_points_exist (R:realType) (t:R):
  exists u:R->R_n R 3,
    (forall z,(u z) ord0=z*(1+t^+2)/FlatExponential.value (1-z)) /\
    (forall z,(u z) (Ordinal (isT:(1<3)%N))=t*(z*(1+t^+2)/FlatExponential.value (1-z))) /\
    (forall z,(u z) ord_max=z) /\
    u 0=0 /\forall z:R,z<1 ->CartanSurface.set (u z).
Proof.
pose a:=fun z:R=>FlatExponential.value (1-z).
pose x:=fun z:R=>z*(1+t^+2)/a z.
pose u:=fun z:R=>[ffun i:'I_3=>if i==ord0 then x z else
  if i==Ordinal (isT:(1<3)%N) then t*x z else z].
have hX z:(u z) ord0=x z by rewrite /u ffunE eqxx.
have hY z:(u z) (Ordinal (isT:(1<3)%N))=t*x z by rewrite /u ffunE /=.
have hZ z:(u z) ord_max=z by rewrite /u ffunE /=.
exists u;split;first exact:hX.
split;first exact:hY.
split;first exact:hZ.
split.
- apply/ffunP=>i;rewrite /u !ffunE /x mul0r mul0r.
  by case:(i==ord0);case:(i==Ordinal (isT:(1<3)%N));rewrite ?mulr0.
- move=>z hz;apply/(cartan_surface_membership (@CartanSurface.laws R)).
  rewrite hX hY hZ.
  have hPositive:0<a z by rewrite /a flat_exponential_positive subr_gt0.
  have hNonzero:a z!=0 by rewrite gt_eqF.
  change (z*((x z)^+2+(t*x z)^+2)=(x z)^+3*a z).
  rewrite /x;field;exact:hNonzero.
Qed.
