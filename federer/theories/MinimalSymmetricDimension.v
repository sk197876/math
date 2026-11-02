(** Federer (1969), 1.7.3, p. 29: minimal invariant subspaces of symmetric
    maps have dimension one. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ModuleQuotient SubspaceCarrier InnerProductUP
  InnerProductRestriction SymmetricEndomorphisms InvariantRestriction
  MinimalInvariantUP EigenvectorExistence InvariantFiniteSpan FiniteSpans
  FiniteSpanSpace SpanningDimensionBound LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [minimal_invariant_positive_dimension]: Federer
    1.7.3, p. 29, the minimal invariant summands are nonzero,
    hence their basis lengths are positive. *)
Lemma minimal_invariant_positive_dimension (R : realFieldType)
    (V : lmodType R) (f : {linear V -> V}) (W : subspace V)
    (hW : is_minimal_invariant_subspace f W) n
    (b : 'I_n -> subspace_space W) (hb : is_basis b) : (0 < n)%N.
Proof.
apply: (@basis_nonzero_positive_dimension R (subspace_space W) n b hb).
have [x [hx hn]] := minimal_invariant_nonzero hW.
exists (subspace_lift hx); apply/eqP=> hz.
have hv := congr1 (@subspace_val R V W) hz.
by rewrite subspace_liftE linear0 in hv; move: hn; rewrite hv eqxx.
Qed.

(** Source for [minimal_symmetric_dimension]: Federer 1.7.3,
    p. 29, symmetric case of the minimal invariant decomposition:
    every minimal nonzero invariant subspace has dimension one. *)
Theorem minimal_symmetric_dimension (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f : {linear V -> V}) (hf : is_symmetric_endomorphism B f)
    (W : subspace V) (hW : is_minimal_invariant_subspace f W)
    n (b : 'I_n -> subspace_space W) (hb : is_basis b) : n = 1%N.
Proof.
have hn := @minimal_invariant_positive_dimension R V f W hW n b hb.
pose C := @restricted_inner_product R V B W.
have hC := @restricted_inner_productP R V B hB W.
pose g := @invariant_restriction R V f W (minimal_invariant_stable hW).
have hg : is_symmetric_endomorphism C g.
  exact: symmetric_invariant_restriction hf.
have [v [lambda [hv heig]]] :=
  @symmetric_unit_eigenvector R (subspace_space W) C hC g hg n b hb hn.
pose x := subspace_val v.
pose e := fun _ : 'I_1 => x.
pose Z := finite_span_subspace e.
have hx : x != 0 := @unit_square_nonzero R V B hB x hv.
have hZW : forall y, Z y -> W y.
  apply: finite_span_subspace_contained => i; exact: subspace_valP.
have hZx : Z x := @finite_span_generator R V 1 e ord0.
have hZeig : f x = lambda *: x.
  have hh := congr1 (@subspace_val R V W) heig.
  by rewrite linearZ in hh.
have hZf : invariant_subspace f Z.
  apply: finite_span_invariant => i.
  exists (fun _ : 'I_1 => lambda); by rewrite big_ord1 hZeig.
have hWZ := @minimal_invariant_minimal R V f W hW Z hZW
  (ex_intro _ x (conj hZx hx)) hZf.
have hs : forall y : subspace_space W, in_finite_span (fun _ : 'I_1 => v) y.
  move=> y; have [c hc] := hWZ _ (subspace_valP y).
  exists c; apply: subspace_val_injective.
  rewrite linear_sum; under eq_bigr do rewrite linearZ.
  exact hc.
have hd := @spanning_dimension_bound R (subspace_space W) n b hb 1
  (fun _ : 'I_1 => v) hs.
apply/eqP; rewrite eqn_leq; apply/andP; exact (conj hd hn).
Qed.
