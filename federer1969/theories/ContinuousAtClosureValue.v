(** General topology supporting the closed maximal-rank subset
    in Federer (1969), 3.1.20, p. 233. Continuity at the limit
    point suffices; no global continuous extension is assumed. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_at_closure_closed_value]: a function
    continuous at b takes b into a closed set C if it takes a
    subset accumulating at b into C. Supporting the relatively
    closed maximal-rank set in Federer 3.1.20, p. 233. *)
Lemma continuous_at_closure_closed_value (T Y:topologicalType) (g:T->Y)
    (S:set T) b (C:set Y) : g @ b --> g b -> closed C ->
  (forall x,S x -> C (g x)) -> closure S b -> C (g b).
Proof.
move=>hg hC hSC hb; apply: contrapT=>hn.
have hnb:=open_nbhs_nbhs (conj (closed_openC hC) hn).
have hpre:=hg (~`C) hnb.
rewrite closureEnbhs in hb.
have [x [hxS hxN]]:=hb S (g @^-1` (~`C)) (fun x hx=>hx) hpre.
exact: hxN (hSC x hxS).
Qed.
