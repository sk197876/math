(** Federer (1969), 3.3.2, pp. 287–288: after the corrected
    strict-superlevel formula, the rational-ray criterion gives a
    Borel function with values in the actual extended real line.
    Expand the general-topology argument from 2.3.2(2), p. 73. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import BorelFunctionUP TopologicalBorel BorelFamilyBasic
  CountableOrderIntervals ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_borel_from_strict_superlevels]: the
    final Borel-function conclusion in Federer 3.3.2,
    p. 288, by the strict upper-ray form of 2.3.2(2),
    p. 73. This general supporting criterion retains both
    infinite values and requires no measure on the domain. *)
Theorem structure_borel_from_strict_superlevels (R:realType)
    (P:topologicalType) (f:P->extended_real_line R):
  (forall b:R,borel_set [set x|(b%:E<f x)%E]) ->is_borel_function f.
Proof.
move=>hUpper.
pose d (q:rat):extended_real_line R:=(ratr q:R)%:E.
have hd:=@extended_rationals_order_dense R.
have hClosed q:borel_set [set x|(f x<=d q)%E].
  have he:[set x|(f x<=d q)%E]=~`[set x|(d q<f x)%E].
    apply/seteqP; split=>x; rewrite /= leNgt; by move/negP.
  rewrite he; exact:(borel_set_complement (hUpper (ratr q))).
have hLower q:borel_set [set x|(f x<d q)%E].
  have he:[set x|(f x<d q)%E]=
      \bigcup_(j in [set j|(d j<d q)%E]) [set x|(f x<=d j)%E].
    apply/seteqP; split=>x.
    - move=>hx; have [j [hxj hjq]]:=hd _ _ hx.
      exists j=>//; exact:(ltW hxj).
    - move=>[j hj hx]; exact:(le_lt_trans hx hj).
  rewrite he; apply:borel_set_countable_union (countableP _) _=>j _; exact:hClosed.
have hInterval c:borel_set (f @^-1` order_family_interval d c).
  have he:order_family_interval d c=
      (if c.1 is Some j then [set y|(d j<y)%E] else setT) `&`
      (if c.2 is Some j then [set y|(y<d j)%E] else setT).
    by case:c=>[[j|] [k|]].
  rewrite he preimage_setI; clear he; apply:(borel_family_binary_intersection (borel_sets_family P)).
  - case:c=>[[j|] [k|]] /=;
      first [exact:hUpper | by rewrite preimage_setT; exact:(open_borel_set openT)].
  - case:c=>[[j|] [k|]] /=;
      first [exact:hLower | by rewrite preimage_setT; exact:(open_borel_set openT)].
move=>U hU.
pose D:=[set c:option rat*option rat|order_family_interval d c `<=` U].
have he:U=\bigcup_(c in D) order_family_interval d c.
  apply/seteqP; split=>x.
  - move=>hx; have [c [hc hSub]]:=@order_family_intervals_refine _
      [the orderTopologicalType _ of order_topology (\bar R)]
      [the countType of (rat:Type)] d hd U hU x hx.
    by exists c.
  - move=>[c hc hx]; exact:(hc x hx).
rewrite he preimage_bigcup; apply:borel_set_countable_union (countableP _) _=>c _.
exact:hInterval.
Qed.
