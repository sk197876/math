(** Federer (1969), 1.7.3, p. 29: minimal invariant subspaces of
    skewsymmetric maps have dimension at most two. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ModuleQuotient SubspaceCarrier InnerProductUP
  InnerProductRestriction SymmetricEndomorphisms InvariantRestriction
  MinimalInvariantUP MinimalSymmetricDimension EigenvectorExistence
  InvariantFiniteSpan CyclicPair FiniteSpans FiniteSpanSpace InfiniteSequence
  SpanningDimensionBound LinearBasis TensorUP Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [minimal_skewsymmetric_dimension]: Federer
    1.7.3, p. 29, skewsymmetric case: on each minimal nonzero
    invariant subspace, an eigenvector x of f squared generates
    the whole subspace together with f(x), so its dimension is at most two. *)
Theorem minimal_skewsymmetric_dimension (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f : {linear V -> V}) (hf : is_skewsymmetric_endomorphism B f)
    (W : subspace V) (hW : is_minimal_invariant_subspace f W)
    n (b : 'I_n -> subspace_space W) (hb : is_basis b) : (n <= 2)%N.
Proof.
have hn := @minimal_invariant_positive_dimension R V f W hW n b hb.
pose C := @restricted_inner_product R V B W.
have hC := @restricted_inner_productP R V B hB W.
pose g := @invariant_restriction R V f W (minimal_invariant_stable hW).
have hg : is_skewsymmetric_endomorphism C g.
  exact: skewsymmetric_invariant_restriction hf.
have hgg := @skewsymmetric_square_symmetric R (subspace_space W) C g hg.
have [v [lambda [hv heig]]] :=
  @symmetric_unit_eigenvector R (subspace_space W) C hC
    (linear_comp g g) hgg n b hb hn.
pose x := subspace_val v.
pose e := ordinal_snoc (fun _ : 'I_1 => x) (f x).
pose Z := finite_span_subspace e.
have hx : x != 0 := @unit_square_nonzero R V B hB x hv.
have hZW : forall y, Z y -> W y.
  apply: finite_span_subspace_contained => i.
  case: (unliftP ord_max i) => [j ->|->].
  - rewrite /e ordinal_snoc_lift; exact: subspace_valP.
  - rewrite /e ordinal_snoc_last; apply: (minimal_invariant_stable hW).
    exact: subspace_valP.
have hZx : Z x.
  apply: in_finite_span_snoc.
  exact (@finite_span_generator R V 1 (fun _ => x) ord0).
have hZeig : f (f x) = lambda *: x.
  have hh := congr1 (@subspace_val R V W) heig.
  by rewrite linearZ in hh.
have hZf : invariant_subspace f Z := @cyclic_pair_invariant R V f x lambda hZeig.
have hWZ := @minimal_invariant_minimal R V f W hW Z hZW
  (ex_intro _ x (conj hZx hx)) hZf.
pose a := ordinal_snoc (fun _ : 'I_1 => v) (g v).
have ha i : subspace_val (a i) = e i.
  case: (unliftP ord_max i) => [j ->|->].
  - by rewrite /a /e !ordinal_snoc_lift.
  - by rewrite /a /e !ordinal_snoc_last.
have hs : forall y : subspace_space W, in_finite_span a y.
  move=> y; have [c hc] := hWZ _ (subspace_valP y).
  exists c; apply: subspace_val_injective.
  rewrite linear_sum.
  have hh : (\sum_i subspace_val (c i *: a i)) = \sum_i c i *: e i.
    apply: eq_bigr => i _; rewrite linearZ.
    exact (congr1 (fun z : V => c i *: z) (ha i)).
  by rewrite hh.
exact (@spanning_dimension_bound R (subspace_space W) n b hb 2 a hs).
Qed.
