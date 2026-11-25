(** General topology supporting Federer (1969), 3.4.10,
    p. 337: a compact set in the
    original domain meets only finitely many members
    of a locally finite family. Reuse the
    existing compact finite-cover theorem. *)
From mathcomp Require Import all_boot finmap boolp classical_sets cardinality topology.
From Federer Require Import LocallyFiniteFamilyUP CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [locally_finite_family_compact]: the
    literal compact-incidence condition in 3.4.10,
    p. 337. No closedness of the
    family members or of the domain is required. *)
Theorem locally_finite_family_compact (X:topologicalType) (J:choiceType)
    (U:set X) (I:set J) (F:J->set X) (C:set X):
  is_locally_finite_family_on U I F ->compact C ->C `<=` U ->
  finite_set (I `&` [set j|exists x,C x /\F j x]).
Proof.
move=>hLocal hCompact hCU.
pose D:set (set X):=[set O|open O /\
  finite_set (I `&` [set j|exists x,O x /\F j x])].
have hCover:C `<=` \bigcup_(O in D) O.
  move=>x hx;have [O [hO [hxO hFinite]]]:=hLocal x (hCU x hx).
  exists O;[by split|exact:hxO].
have [B hBD hBCover]:=@compact_open_finite_cover X [the choiceType of set X]
  D (fun O=>O) C hCompact (fun O hO=>hO.1) hCover.
have hFinite:finite_set (\bigcup_(O in [set` B])
    (I `&` [set j|exists x,O x /\F j x])).
  apply:bigcup_finite;first exact:finite_fset.
  move=>O hO;have /asboolP hD:=hBD O hO;exact:hD.2.
apply:(sub_finite_set _ hFinite)=>j [hj [x [hxC hxF]]].
have [O hOB hxO]:=hBCover x hxC.
exists O;first exact:hOB.
split;first exact:hj.
by exists x;split.
Qed.
