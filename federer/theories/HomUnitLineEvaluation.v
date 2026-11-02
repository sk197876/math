(** Federer (1969), 3.2.28(2), printed p. 264:
    evaluation at a unit top vector is an isometry from
    Hom(Lambda^m R^m,Lambda^m R^n) to Lambda^m R^n.
    This supporting unit-line calculation is independent of
    the target dimension and uses only 1.7.9, p. 35. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom InnerProductUP InnerNorm LinearBasis
  FiniteBasisCriterion HomInner HomInnerCoordinates OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unit_spanning_singleton_basis]: a nonzero
    vector spanning a line is a basis, by 1.1.2 and 1.6.1,
    pp. 10 and 23–24. Supporting the evaluation isometry
    in Federer 3.2.28(2), p. 264. *)
Lemma unit_spanning_singleton_basis (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (z:V):
  inner_norm hB z= 1 ->(forall x,exists c:R,x=c*:z) ->
  is_basis (fun _:'I_1=>z).
Proof.
move=>hz hSpan.
have hNz:z!=0.
  apply/eqP=>hZero; move:hz; rewrite hZero inner_norm0=>/eqP.
  by rewrite eq_sym oner_eq0.
apply:finite_basis_criterion.
- move=>c hc i; rewrite ord1 in hc *.
  rewrite big_ord1 in hc.
  move/eqP:hc; rewrite scaler_eq0 (negbTE hNz) orbF=>/eqP; exact.
- move=>x; have [c hc]:=hSpan x.
  exists (fun _=>c); by rewrite big_ord1.
Qed.

(** Source for [hom_unit_line_evaluation_inner]: evaluation
    at a unit vector spanning the source preserves the
    inner product of Hom, supporting the isometry in
    Federer 3.2.28(2), p. 264, by the orthonormal
    sum formula of 1.7.9, p. 35. *)
Theorem hom_unit_line_evaluation_inner (R:realType) (V W:lmodType R)
    (B:V->V->R) (C:W->W->R) (hB:is_inner_product B) (hC:is_inner_product C)
    n (b:'I_n->V) (hb:is_basis b) (z:V):
  inner_norm hB z= 1 ->(forall x,exists c:R,x=c*:z) ->
  forall f g:Hom V W,hom_inner hB hC hb f g=C (f z) (g z).
Proof.
move=>hz hSpan f g.
have hd:=@unit_spanning_singleton_basis R V B hB z hz hSpan.
have ho:orthonormal_family B (fun _:'I_1=>z).
  move=>i j; rewrite !ord1 eqxx.
  by rewrite -[B z z](inner_norm_sqr hB) hz expr1n.
rewrite (@hom_inner_orthonormal_sum R V W B C hB hC n b hb
  1 (fun _:'I_1=>z) hd ho) big_ord1.
reflexivity.
Qed.
