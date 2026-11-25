(** Federer (1969), 3.2.22, pp. 259–260: glue
    the local Borel Jacobian weights on countably many
    disjoint compact chart pieces. Use only the abstract
    agreement and zero-outside laws of 2.5.10, p. 101. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality topology.
From Federer Require Import DisjointFunctionGluingUP TopologicalBorel BorelFamilyBasic
  BorelFunctionUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [borel_disjoint_function_gluing]: supporting
    countable Jacobian weights in Federer 3.2.22,
    pp. 259–260. Each Borel preimage is the
    countable union of its Borel piece preimages, together
    with the complement of the support when the open set
    contains zero. Only the exposed gluing laws are used. *)
Lemma borel_disjoint_function_gluing (R:realType) (X:topologicalType) (I:choiceType)
    (D:set I) (B:I->set X) (f:I->X->real_line_metric R) (g:X->real_line_metric R):
  countable D ->(forall i,D i ->borel_set (B i)) ->
  (forall i,D i ->is_borel_function (f i)) ->
  @is_disjoint_function_gluing R X I D B f g ->is_borel_function g.
Proof.
move=>hCount hB hF hGlue U hU.
pose S:=\bigcup_(i in D) B i.
have hSB:borel_set S.
  apply:(borel_set_countable_union hCount)=>i hi; exact:(hB i hi).
have hPieces:borel_set (\bigcup_(i in D) (B i `&` (f i @^-1` U))).
  apply:(borel_set_countable_union hCount)=>i hi.
  exact:(borel_family_binary_intersection (borel_sets_family X) (hB i hi) (hF i hi U hU)).
have hElse:borel_set [set x|~S x /\ U 0].
  have [hZero|hZero]:=pselect (U 0).
  - have hEq:[set x|~S x /\ U 0]=~` S.
      apply/seteqP; split=>x; first by move=>[].
      by move=>hx; split.
    rewrite hEq; exact:borel_set_complement hSB.
  - have hEq:[set x|~S x /\ U 0]=set0.
      apply/seteqP; split=>[x [_ hx]|x []]; exact:hZero hx.
    rewrite hEq; exact:open_borel_set open0.
have hEq:g @^-1` U=(\bigcup_(i in D) (B i `&` (f i @^-1` U))) `|`
    [set x|~S x /\ U 0].
  apply/seteqP; split=>x.
  - move=>hx; have [hSx|hSx]:=pselect (S x).
    + have [i hi hBx]:=hSx; left; exists i; first exact hi.
      split; first exact hBx; change (U (f i x)).
      by rewrite -(hGlue.1 i x hi hBx).
    + right; split; first exact hSx; by rewrite -(hGlue.2 x hSx).
  - move=>[[i hi [hBx hFx]]|[hSx hZero]].
    + change (U (g x)); by rewrite (hGlue.1 i x hi hBx).
    + change (U (g x)); by rewrite (hGlue.2 x hSx).
rewrite hEq; exact:(borel_family_binary_union (borel_sets_family X) hPieces hElse).
Qed.

(** Source for [nonnegative_disjoint_function_gluing]:
    nonnegative local Jacobian weights in Federer 3.2.22,
    pp. 259–260, stay nonnegative after gluing.
    The outside value is zero, as specified by the
    density gluing convention of 2.5.10, p. 101. *)
Lemma nonnegative_disjoint_function_gluing (R:realType) (X I:Type)
    (D:set I) (B:I->set X) (f:I->X->R) (g:X->R):
  (forall i x,D i ->B i x ->0<=f i x) ->
  @is_disjoint_function_gluing R X I D B f g ->forall x,0<=g x.
Proof.
move=>hF hGlue x; have [hx|hx]:=pselect ((\bigcup_(i in D) B i) x).
- have [i hi hBx]:=hx; rewrite (hGlue.1 i x hi hBx); exact:(hF i x hi hBx).
- by rewrite (hGlue.2 x hx).
Qed.
