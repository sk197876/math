(** Federer (1969), 3.4.10, p. 337:
    finitely many germwise finite-mass dominations hold
    on one actual neighbourhood. This connects
    the local analytic exceptional germs to the
    outer measure of the original singular set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import SetGermUP SetGermOrder MeasureUP MeasureBasic
  MeasureFiniteIndexedMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_germ_local_mass]: the local
    finite H^(m-1) bound on the exceptional union
    in 3.4.10, p. 337. Finite ordinary
    neighbourhood intersections and the existing finite-union
    mass bound suffice; no representative equality or
    measurability of the original sets is needed. *)
Theorem finite_germ_local_mass (R:realType) (X:topologicalType) (J:finType)
    (a:X) (mu:set X->\bar R) (S K:J->set X):
  is_measure mu ->
  (forall j,set_germ_subset (@set_germ X a (S j)) (@set_germ X a (K j))) ->
  (forall j,mu (K j)< +oo) ->
  exists W:set X,open W /\W a /\mu ((\bigcup_j S j) `&` W)< +oo.
Proof.
move=>hMu hContained hMass.
have hEach j:exists U:set X,open U /\U a /\forall x,S j x ->U x ->K j x.
  exact:(@set_germ_subset_original X a (S j) (K j)).1 (hContained j).
have [U hU]:=choice hEach.
pose C:set X:=\bigcup_j (~` U j).
have hC:closed C.
  apply:(closed_bigcup (@finite_finset J setT))=>j _.
  exact:open_closedC (hU j).1.
pose W:set X:=~` C.
have hW:open W:=closed_openC hC.
have haW:W a.
  move=>[j _ hNot];exact:hNot (hU j).2.1.
have hSubset:(\bigcup_j S j) `&` W `<=` \bigcup_j K j.
  move=>x [[j _ hxS] hxW];exists j;first exact:Logic.I.
  apply:((hU j).2.2 x hxS).
  apply:contrapT=>hxNot;apply:hxW;by exists j.
exists W;split;first exact:hW.
split;first exact:haW.
exact:(le_lt_trans (measure_mono hMu hSubset)
  (measure_finite_indexed_union_finite_mass hMu hMass)).
Qed.
