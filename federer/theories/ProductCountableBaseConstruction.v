(** General topology supporting Federer (1969), 2.2.11, p. 68: the
    countable-base construction is applied to Z=Y times N, in particular N
    times N. Products of two enumerated bases have an enumerated base by
    natural-pair indexing. Source context: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import NaturalPairing CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_base_refines_neighborhood]: supporting
    neighborhood form of the base property in Federer 2.2.11,
    p. 68. Every neighborhood contains an open neighborhood,
    which is refined by one of the given basic sets. *)
Lemma countable_base_refines_neighborhood (T : topologicalType) (U : nat -> set T)
    (hU : is_countable_open_base U) x V :
  nbhs x V -> exists i, U i x /\ U i `<=` V.
Proof.
rewrite nbhsE=> -[W [hW hx] hWV].
have [i [hi his]] := @countable_base_refines T U hU W hW x hx.
exists i; split=> //; exact: subset_trans his hWV.
Qed.

(** Source for [product_basic_rectangle_open]: supporting
    product topology for Federer 2.2.11, p. 68:
    the product of two open basic sets is open. *)
Lemma product_basic_rectangle_open (T V : topologicalType) (A : set T) (B : set V) :
  open A -> open B -> open (A `*` B).
Proof.
move=> hA hB; rewrite openE=> -[x y] [hx hy].
have hnA : nbhs x A by rewrite openE in hA; exact: hA x hx.
have hnB : nbhs y B by rewrite openE in hB; exact: hB y hy.
exists (A,B); first by split.
by move=> [u v] huv.
Qed.

(** Source for [product_countable_open_base_exists]: supporting
    countable base of the product Z used in Federer 2.2.11,
    p. 68. Enumerate pairs of factor basic sets, with an
    additional empty first member for the closed-set coding convention. *)
Theorem product_countable_open_base_exists (T V : topologicalType)
    (U : nat -> set T) (W : nat -> set V) :
  is_countable_open_base U -> is_countable_open_base W ->
  exists B : nat -> set (T * V), is_countable_open_base B.
Proof.
move=> hU hW; have [encode [decode [he hd]]] := natural_pairing_exists.
pose B i := if i is k.+1 then U (decode k).1 `*` W (decode k).2 else set0.
exists B; constructor.
- move=> [|k]; first exact: open0.
  apply: product_basic_rectangle_open; exact: countable_base_open.
- by [].
- move=> O hO [x y] hxy.
  have hn : nbhs (x,y) O by rewrite openE in hO; exact: hO _ hxy.
  have [[A D] [hA hD] had] := hn.
  have [i [hi his]] := countable_base_refines_neighborhood hU hA.
  have [j [hj hjs]] := countable_base_refines_neighborhood hW hD.
  exists (encode (i,j)).+1; rewrite /B he /=; split; first by split.
  move=> [u v] [hu hv]; apply: had; split; [exact: his u hu|exact: hjs v hv].
Qed.
