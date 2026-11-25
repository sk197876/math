(** Supporting Federer (1969), 3.4.8(5), p. 328:
    pairs of original germ witnesses have a common
    increasing compact cover. Compact product topology
    is background; the common index is proved from
    the independent cover laws. *)
From mathcomp Require Import all_boot all_order boolp classical_sets topology.
From Federer Require Import IncreasingCompactCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [increasing_compact_cover_pair]: two
    original witness sets with increasing compact covers
    have a compact cover of their exact Cartesian
    product, supporting 3.4.8(5), p. 328. *)
Lemma increasing_compact_cover_pair (T U:topologicalType)
  (S:set T) (D:set U) (K:nat->set T) (L:nat->set U):
  is_increasing_compact_cover S K ->is_increasing_compact_cover D L ->
  @is_increasing_compact_cover (T*U)%type (S `*` D) (fun n=>K n `*` L n).
Proof.
move=>hK hL;constructor.
- move=>n;exact:(compact_setX (@increasing_compact_cover_compact T S K hK n)
    (@increasing_compact_cover_compact U D L hL n)).
- move=>n [x y] [hx hy];split.
  + exact:(@increasing_compact_cover_contained T S K hK n x hx).
  + exact:(@increasing_compact_cover_contained U D L hL n y hy).
- move=>m n hmn [x y] [hx hy];split.
  + exact:(@increasing_compact_cover_monotone T S K hK m n hmn x hx).
  + exact:(@increasing_compact_cover_monotone U D L hL m n hmn y hy).
- move=>[x y] [hx hy].
  have [m hm]:=@increasing_compact_cover_covers T S K hK x hx.
  have [n hn]:=@increasing_compact_cover_covers U D L hL y hy.
  exists (maxn m n);split.
  + exact:(@increasing_compact_cover_monotone T S K hK m (maxn m n) (leq_maxl m n) x hm).
  + exact:(@increasing_compact_cover_monotone U D L hL n (maxn m n) (leq_maxr m n) y hn).
Qed.
