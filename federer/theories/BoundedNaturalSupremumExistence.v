(** Federer (1969), 3.4.10, p. 337:
    finite-dimensional local dimensions have a unique attained
    supremum. Reuse the finite natural maximum theorem;
    only the bounded range needs to be collected. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import BoundedNaturalSupremumUP FiniteNaturalMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [bounded_natural_supremum_exists]: existence of
    the supremum in 3.4.10, p. 337,
    for a bounded natural-valued family, including the
    explicitly totalized empty case. *)
Theorem bounded_natural_supremum_exists (X:Type) (S:set X) (q:X->nat) n:
  (forall x,S x ->(q x<=n)%N) ->
  exists d,is_bounded_natural_supremum S q d.
Proof.
move=>hBound.
case:(pselect (S=set0))=>[hEmpty|hNonempty].
- exists 0%N;constructor.
  + by rewrite hEmpty=>x.
  + by move=>h;exact:False_ind (h hEmpty).
  + by move=>_.
- pose F:=filter (fun k=>asbool (exists x,S x /\q x=k)) (iota 0 n.+1).
  have hMember k:k \in F <->exists x,S x /\q x=k.
    split.
    + by rewrite mem_filter=>/andP[/asboolP h _].
    + move=>[x [hx hEqual]];rewrite mem_filter;apply/andP;split.
      * apply/asboolP;exists x;by split.
      * rewrite mem_iota add0n leq0n /= -hEqual;exact:hBound x hx.
  have [x hx]:exists x,S x.
    apply:contrapT=>hNone;apply:hNonempty;apply/seteqP;split.
    + move=>x hx;apply:hNone;by exists x.
    + by move=>x.
  have hF:F!=[::].
    apply/eqP=>hEmpty;have h:=(hMember (q x)).2 (ex_intro _ x (conj hx erefl)).
    by rewrite hEmpty in_nil in h.
  have [d [hD hMaximum]]:=@finite_natural_maximum (Choice.clone nat _) F id hF.
  exists d;constructor.
  + move=>y hy;apply:hMaximum;apply/hMember;exists y;by split.
  + move=>_;exact:(hMember d).1 hD.
  + by move=>hEmpty;exact:False_ind (hNonempty hEmpty).
Qed.

(** Source for [bounded_natural_supremum_unique]: the supremum
    in 3.4.10, p. 337, depends only
    on the local dimensions, not on a selected
    finite range or maximizing point. *)
Theorem bounded_natural_supremum_unique (X:Type) (S:set X) (q:X->nat) d e:
  is_bounded_natural_supremum S q d ->
  is_bounded_natural_supremum S q e ->d=e.
Proof.
move=>hD hE;case:(pselect (S=set0))=>[hEmpty|hNonempty].
- by rewrite (bounded_natural_supremum_empty hD hEmpty)
    (bounded_natural_supremum_empty hE hEmpty).
- have [x [hx hX]]:=bounded_natural_supremum_attained hD hNonempty.
  have [y [hy hY]]:=bounded_natural_supremum_attained hE hNonempty.
  apply/eqP;rewrite eqn_leq;apply/andP;split.
  + rewrite -hX;exact:(@bounded_natural_supremum_upper X S q e hE x hx).
  + rewrite -hY;exact:(@bounded_natural_supremum_upper X S q d hD y hy).
Qed.
