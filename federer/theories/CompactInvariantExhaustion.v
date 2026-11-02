(** General topology supporting Federer (1969), 3.2.28(4),
    pp. 266–267: make a compact cover increasing
    and invariant under the antipodal involution. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_invariant_exhaustion]: supporting
    exhaustion for the two-to-one area argument in
    Federer 3.2.28(4), pp. 266–267. Every
    selected compact piece is invariant, so it retains
    both actual points in each nonempty fibre. *)
Theorem compact_invariant_exhaustion (T:topologicalType)
    (S:set T) (f:T->T) (K:nat->set T):
  continuous f ->cancel f f ->(forall x,S x ->S (f x)) ->
  (forall i,compact (K i) /\K i `<=` S) ->S=\bigcup_i K i ->
  exists L:nat->set T,
    (forall i,compact (L i) /\L i `<=` S /\forall x,L i x ->L i (f x)) /\
    (forall i,L i `<=` L i.+1) /\S=\bigcup_i L i.
Proof.
move=>hF hFF hS hK hCover.
pose L:=fix loop (i:nat):set T:=
  if i is j.+1 then (loop j `|` K j) `|` (f @` K j) else set0.
have hL i:compact (L i) /\L i `<=` S /\forall x,L i x ->L i (f x).
  elim:i=>[|i [hLC [hLS hLI]]].
  - split; first exact:compact0.
    by split=>[x []|x []].
  - split.
    + apply:compactU; first exact:compactU hLC (hK i).1.
      exact:continuous_compact (continuous_subspaceT hF) (hK i).1.
    + split.
      * move=>x [[hx|hx]|[y hy <-]].
        -- exact:hLS x hx.
        -- exact:(hK i).2 x hx.
        -- exact:hS y ((hK i).2 y hy).
      * move=>x [[hx|hx]|[y hy <-]].
        -- left; left; exact:hLI x hx.
        -- right; by exists x.
        -- rewrite hFF; left; right; exact hy.
exists L; split; first exact hL.
split.
- move=>i x hx; left; by left.
- apply/seteqP; split=>x.
  + move=>hx; have [i _ hi]: (\bigcup_i K i) x by rewrite -hCover.
    exists i.+1; first exact I.
    left; by right.
  + move=>[i _ hx]; exact:(hL i).2.1 x hx.
Qed.
