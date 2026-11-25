(** Federer (1969), 3.4.8(11), p. 333:
    a finite stratum decomposition near a
    point bounds the actual components meeting
    a smaller neighbourhood. The strata are
    chosen inside the original analytic representative;
    no analytic continuation outside that representative
    is needed for this induction step. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import SetGermUP SetGermExistence FiniteComponentCoverAssembly
  ComponentFinitenessAmbientInclusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_strata_local_component_finiteness]:
    the induction hypothesis gives local component
    finiteness of H in 3.4.8(11),
    p. 333. Keep all actual strata
    inside the given representative H when
    choosing their defining neighbourhoods. *)
Theorem finite_strata_local_component_finiteness (X:topologicalType) (I:finType)
    (a:X) (H:set X) (S:I->set X):
  (forall i,S i `<=` H) ->
  (forall i,finite_set (connected_component (S i) @` S i)) ->
  @set_germ X a (\bigcup_i S i) = @set_germ X a H ->
  exists U:set X,open U /\ U a /\
    finite_set (connected_component H @` (H `&` U)).
Proof.
move=>hSub hFinite hGerm.
pose B:=\bigcup_i S i.
have hBFinite:finite_set (connected_component B @` B).
  apply:(@finite_component_cover_assembly X I setT S B).
  - exact:finite_finset.
  - by move=>i _;exact:hFinite i.
  - move=>i _ x hx;by exists i.
  - move=>x [i _ hi];by exists i;split.
have hBH:B `<=` H by move=>x [i _ hi];exact:hSub i x hi.
have hAmbientFinite:=component_finiteness_ambient_inclusion hBH hBFinite.
have [U [hU [ha hEqual]]]:=(@set_germ_equality_original X a B H).1 hGerm.
exists U;split;first exact:hU.
split;first exact:ha.
apply:(sub_finite_set _ hAmbientFinite)=>C [x [hHx hUx] <-].
have hBx:B x.
  have h:(B `&` U) x by rewrite hEqual;split.
  exact:h.1.
by exists x.
Qed.
