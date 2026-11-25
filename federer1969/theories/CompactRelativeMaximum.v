(** Federer (1969), 3.4.8(11), p. 333:
    Psi attains a maximum on the
    compact closure of a component. This
    relative-continuity adapter extends the interface of
    CompactMaximum without extending the function. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_compact_relative_maximum]:
    the compact maximum step in 3.4.8(11),
    p. 333. Continuity is needed only
    on the actual compact set, as
    in Federer's original argument. *)
Theorem continuous_compact_relative_maximum (R:realType) (X:topologicalType)
    (K:set X) (f:X->R^o):
  K !=set0 ->compact K ->{within K,continuous f} ->
  exists x,K x /\ forall y,K y ->f y<=f x.
Proof.
move=>hK hCompact hContinuous.
have hNonempty:f @` K !=set0:=image_nonempty f hK.
have hImageCompact:compact (f @` K):=continuous_compact hContinuous hCompact.
have hSup:has_sup (f @` K):=compact_has_sup hNonempty hImageCompact.
have hSupremum:supremums (f @` K) (sup (f @` K)).
  split;first exact:sup_upper_bound hSup.
  move=>b hb;exact:ge_sup hNonempty hb.
have [x hx hValue]:=itv_closed_supremums hNonempty
  (compact_closed (@norm_hausdorff R _) hImageCompact) hSupremum.
exists x;split;first exact:hx.
move=>y hy;rewrite hValue;apply:(@sup_upper_bound R (f @` K) hSup).
by exists y.
Qed.
