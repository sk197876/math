(** Federer (1969), 2.6.6, p. 120: the full product of the compact Hausdorff
    factor spaces is compact Hausdorff and nonempty. Nonemptiness follows
    from the factor normalizations, rather than being silently assumed.
    Tychonoff is general-topology background. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice DaniellIntegralUP
  DaniellIntegralAlgebra MonotoneDaniellIntegralUP MonotoneDaniellIntegralSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normalized_daniell_space_nonempty]: normalization
    mu(1)=1 excludes an empty factor in Federer 2.6.6, p. 120. *)
Lemma normalized_daniell_space_nonempty (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) :
  is_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  A (fun _=>1) = 1 -> exists x : X, True.
Proof.
move=> hA hA1; apply: contrapT=> hn.
have he : (fun _ : X=>(1 : R))=(fun _=>0).
  apply: funext=> x; exfalso; apply: hn; by exists x.
rewrite he (@daniell_integral_zero R X _ A hA _ (@compactly_supported_zero_function R X)) in hA1.
by move: hA1; move/eqP; rewrite eq_sym oner_eq0.
Qed.

(** Source for [normalized_daniell_product_nonempty]: existence of
    a full product point in Federer 2.6.6, p. 120, from the
    given factor integrals of mass one and classical choice. *)
Theorem normalized_daniell_product_nonempty (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R) :
  (forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i)) ->
  (forall i, A i (fun _=>1) = 1) -> exists x : prod_topology Y, True.
Proof.
move=> hA hA1.
have hne i := normalized_daniell_space_nonempty (monotone_daniell_integral_is_daniell (hA i)) (hA1 i).
by exists (fun i=>sval (cid (hne i))).
Qed.

(** Source for [compact_factor_product_compact]: compactness of X
    in Federer 2.6.6, p. 120, by the general-topology product theorem. *)
Lemma compact_factor_product_compact (I : choiceType) (Y : I -> topologicalType) :
  (forall i, compact (@setT (Y i))) -> compact (@setT (prod_topology Y)).
Proof.
move=> hc; have h := @tychonoff I Y (fun _=>setT) hc.
by apply: (subclosed_compact closedT h)=> x _ i.
Qed.

(** Source for [hausdorff_factor_product_hausdorff]: Hausdorff
    separation of X in Federer 2.6.6, p. 120. *)
Lemma hausdorff_factor_product_hausdorff (I : choiceType) (Y : I -> topologicalType) :
  (forall i, hausdorff_space (Y i)) -> hausdorff_space (prod_topology Y).
Proof. exact: hausdorff_product. Qed.
