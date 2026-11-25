(** Federer (1969), 3.1.18, p. 229: full source rank means that
    the linear map is univalent. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom LinearBasis FiniteIndependence
  FiniteBasisCriterion FiniteBasisComparison FiniteDimension IndependentMap
  LinearRankAtLeast.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [linear_full_rankP]: injectivity is the rank-m
    threshold for an m-dimensional source, supporting the inverse-
    function step in Federer 3.1.18, p. 229. *)
Lemma linear_full_rankP (K:fieldType) (X Y:lmodType K) m (b:'I_m->X)
    (hb:is_basis b) (L:Hom X Y) : linear_rank_at_least L m <-> injective L.
Proof.
split.
- move=>[e he].
  have hi:finite_independent e.
    move=>c hc; apply: he.
    have h := congr1 (hom_as_linear L) hc.
    rewrite linear_sum linear0 in h.
    have hs : (\sum_i hom_as_linear L (c i*:e i))=\sum_i c i*:L (e i).
      apply: eq_bigr=>i _; by rewrite linearZ hom_as_linearE.
    by rewrite hs in h.
  have heb:is_basis e.
    apply: (@finite_independent_basis K (finite_basis_vect hb) m e).
    + by rewrite finite_basis_dimension card_ord.
    + exact hi.
  exact (@independent_basis_image_injective K X Y m e heb (hom_as_linear L) he).
- move=>hL; exists b; exact: finite_independent_map hL (finite_basis_independent hb).
Qed.
