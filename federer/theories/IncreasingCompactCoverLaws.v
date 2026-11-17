(** Federer (1969), 3.4.8(5), p. 328:
    finite products and continuous images preserve the
    auxiliary compact covers used in the original proof. *)
From mathcomp Require Import all_boot all_order boolp classical_sets topology.
From Federer Require Import IncreasingCompactCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [increasing_compact_cover_finite_uniform]: a
    finite family of original points has one common
    cover index, supporting the finite coefficient maps
    in 3.4.8(5), p. 328. Empty families remain. *)
Lemma increasing_compact_cover_finite_uniform (T:topologicalType) (S:set T)
    (K:nat->set T) (hK:is_increasing_compact_cover S K) (I:finType) (f:I->T):
  (forall i,S (f i)) ->exists n,forall i,K n (f i).
Proof.
move=>hS.
have hEach i:exists n,K n (f i):=increasing_compact_cover_covers hK (hS i).
have [N hN]:=choice hEach.
exists (\max_i N i)=>i.
exact:(increasing_compact_cover_monotone hK (leq_bigmax i) (hN i)).
Qed.

(** Source for [increasing_compact_cover_continuous_image]:
    a continuous map gives an exact countable compact
    cover of its original image, supporting the ideal
    images in 3.4.8(5), p. 328. *)
Theorem increasing_compact_cover_continuous_image (T U:topologicalType)
    (S:set T) (K:nat->set T) (f:T->U):
  is_increasing_compact_cover S K ->continuous f ->
  is_increasing_compact_cover (f @` S) (fun n=>f @` K n).
Proof.
move=>hK hf;constructor.
- move=>n;apply:continuous_compact;last exact:increasing_compact_cover_compact hK n.
  exact:continuous_subspaceT hf.
- move=>n y [x hx <-];exists x;last reflexivity.
  exact:(@increasing_compact_cover_contained T S K hK n x hx).
- move=>m n hmn y [x hx <-];exists x;last reflexivity.
  exact:(@increasing_compact_cover_monotone T S K hK m n hmn x hx).
- move=>y [x hx <-].
  have [n hn]:=increasing_compact_cover_covers hK hx.
  exists n;by exists x.
Qed.
