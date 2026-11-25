(** Federer (1969), 3.2.36, pp. 272--273:
    supporting exact closure of Cartesian sets
    in the original-source product reduction. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [topological_cartesian_closure]:
    general topology supporting the unrestricted
    convex-factor product formula in Federer
    3.2.36, pp. 272--273.
    The closure of a Cartesian set is
    the Cartesian set of the two closures.
    Product neighbourhoods prove both inclusions;
    no source measurability or compactness is
    required for this supporting set identity. *)
Lemma topological_cartesian_closure (X Y:topologicalType) (A:set X) (B:set Y):
  closure (A `*` B)=closure A `*` closure B.
Proof.
apply/seteqP; split.
- move=>[x y] hXY; split.
  + move=>U hU.
    have hProduct:nbhs (x,y) (U `*` @setT Y).
      exists (U,@setT Y); first by split; [exact:hU|exact:filterT].
      by move=>[u v] huv.
    have [[a b] [[ha hb] [haU _]]]:=hXY _ hProduct.
    by exists a.
  + move=>V hV.
    have hProduct:nbhs (x,y) (@setT X `*` V).
      exists (@setT X,V); first by split; [exact:filterT|exact:hV].
      by move=>[u v] huv.
    have [[a b] [[ha hb] [_ hbV]]]:=hXY _ hProduct.
    by exists b.
- move=>[x y] [hX hY] U hU.
  have [[V W] [hV hW] hProduct]:=hU.
  have [a [ha haV]]:=hX V hV.
  have [b [hb hbW]]:=hY W hW.
  exists (a,b); split; first by split.
  exact:hProduct (a,b) (conj haV hbW).
Qed.
