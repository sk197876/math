(** Federer (1969), 2.6.6, p. 120: finite products obtained by successive
    coordinate integrations. Their linearity, monotonicity and normalization
    follow by finite induction. These are construction lemmas; the infinite
    product will be exposed by its marginal laws. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP CompactUniformNorm FunctionLatticeUP
  CoordinateDaniellOperator CoordinateDaniellOrder CoordinateDaniellCommutation
  CommutingOperatorFolds MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Fold.
Variables (R : realType) (I : choiceType) (Y : I -> topologicalType).
Variables (A : forall i, (Y i -> R) -> R).
Hypotheses (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i))).
Hypothesis hX : compact (@setT (prod_topology Y)).
Hypothesis hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (@A i).
Hypothesis hA1 : forall i, @A i (fun _=>1) = 1.
Arguments hh i : clear implicits.
Arguments hc i : clear implicits.
Arguments hA i : clear implicits.
Arguments hA1 i : clear implicits.
Local Notation K := (@compactly_supported_continuous_functions R (prod_topology Y)).
Local Notation U := (coordinate_daniell_operator A).

(** Source for [coordinate_daniell_fold_membership]: successive
    integrations preserve K(X), supporting Federer 2.6.6, p. 120. *)
Lemma coordinate_daniell_fold_membership (s : seq I) f : K f -> K (foldr U f s).
Proof.
apply: operator_fold_preserves_domain=> i g hg.
exact (@coordinate_daniell_operator_preserves_continuity R I Y A i (hh i) (hc i) hX
  (monotone_daniell_integral_is_daniell (hA i)) g hg).
Qed.

(** Source for [coordinate_daniell_fold_add]: linearity of the
    finite product, Federer 2.6.6, p. 120, proved by induction
    on the coordinate integrations of 2.6.4. *)
Lemma coordinate_daniell_fold_add (s : seq I) f g : K f -> K g ->
  foldr U (fun x=>f x+g x) s=(fun x=>foldr U f s x+foldr U g s x).
Proof.
move=> hf hg; elim: s=> [|i s ih] //=; rewrite ih.
exact (@coordinate_daniell_operator_add R I Y A i (hc i) (monotone_daniell_integral_is_daniell (hA i))
  _ _ (coordinate_daniell_fold_membership s hf) (coordinate_daniell_fold_membership s hg)).
Qed.

(** Source for [coordinate_daniell_fold_scale]: real homogeneity of
    the finite product, Federer 2.6.6, p. 120. *)
Lemma coordinate_daniell_fold_scale (s : seq I) c f : K f ->
  foldr U (fun x=>c*f x) s=(fun x=>c*foldr U f s x).
Proof.
move=> hf; elim: s=> [|i s ih] //=; rewrite ih.
exact (@coordinate_daniell_operator_scale R I Y A i (hc i) (monotone_daniell_integral_is_daniell (hA i))
  c _ (coordinate_daniell_fold_membership s hf)).
Qed.

(** Source for [coordinate_daniell_fold_monotone]: monotonicity of
    finite products, Federer 2.6.6, p. 120. *)
Lemma coordinate_daniell_fold_monotone (s : seq I) f g : K f -> K g ->
  function_le f g -> function_le (foldr U f s) (foldr U g s).
Proof.
move=> hf hg hfg; elim: s=> [|i s ih] //=.
exact (@coordinate_daniell_operator_monotone R I Y A i (hc i) (hA i)
  _ _ (coordinate_daniell_fold_membership s hf) (coordinate_daniell_fold_membership s hg) ih).
Qed.

(** Source for [coordinate_daniell_fold_one]: normalization of all
    finite products, including the empty product, Federer 2.6.6, p. 120. *)
Lemma coordinate_daniell_fold_one (s : seq I) : foldr U (fun _=>1) s=(fun _=>1).
Proof.
elim: s=> [|i s ih] //=; rewrite ih; exact: coordinate_daniell_operator_one (hA1 i).
Qed.

(** Source for [coordinate_daniell_fold_permutation]: independence of
    finite integration order, supporting the well-defined finite products
    in Federer 2.6.6, p. 120. *)
Theorem coordinate_daniell_fold_permutation (s t : seq I) f :
  K f -> perm_eq s t -> foldr U f s=foldr U f t.
Proof.
apply: operator_fold_permutation.
- move=> i g hg; exact (@coordinate_daniell_operator_preserves_continuity R I Y A i (hh i) (hc i) hX
    (monotone_daniell_integral_is_daniell (hA i)) g hg).
- move=> i j g hg; case: (eqVneq j i)=> [->|hji]; first by [].
  exact (@coordinate_daniell_operators_commute R I Y A j i hji (hh j) (hc j) (hh i) (hc i)
    (monotone_daniell_integral_is_daniell (hA j)) (monotone_daniell_integral_is_daniell (hA i)) g hg).
Qed.
End Fold.
