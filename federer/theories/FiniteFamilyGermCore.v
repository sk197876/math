(** Federer (1969), 3.4.8(12), p. 335:
    discard the finitely many stratum components whose
    closures miss the original centre. Their closed
    union misses one actual neighbourhood, so the
    remaining components represent exactly the same germ. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import SetGermUP SetGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_family_germ_core]: the component
    selection in the proof of 3.4.8(12), p. 335.
    This supporting topological statement applies to every
    finite family of actual sets. *)
Theorem finite_family_germ_core (X:topologicalType) a (F:set (set X)):
  finite_set F ->
  @set_germ X a (\bigcup_(C in [set C|F C /\closure C a]) C) =
    @set_germ X a (\bigcup_(C in F) C).
Proof.
move=>hF.
pose Bad:set (set X):=[set C|F C /\~closure C a].
pose K:set X:=\bigcup_(C in Bad) closure C.
have hBad:finite_set Bad.
  apply:(sub_finite_set _ hF)=>C hC;exact:hC.1.
have hK:closed K:=closed_bigcup hBad (fun C hC=>@closed_closure X C).
have haK:~K a by move=>[C [_ hNot] hCa];exact:hNot hCa.
apply/set_germ_equality_original.
exists (~` K);split;first exact:closed_openC hK.
split;first exact:haK.
apply/seteqP;split.
- move=>x [[C [hCF hClosure] hxC] hxK];split;last exact:hxK.
  by exists C.
- move=>x [[C hCF hxC] hxK];split;last exact:hxK.
  exists C;last exact:hxC.
  split;first exact:hCF.
  apply:contrapT=>hNot;apply:hxK.
  exists C;first by split.
  exact:subset_closure hxC.
Qed.
