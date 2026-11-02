(** Federer (1969), 2.10.35, printed p. 197: in equal source and target
    dimension, the orthogonal projections are orthogonal automorphisms.
    Their images preserve actual Euclidean Lebesgue measure by 2.7.16(1), p.
    135. Prove these facts through the adjoint and orthogonal-inverse laws,
    without choosing a matrix representation. Neither passage states this
    measure equality. No relevant working-erratum correction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  CoordinateProjection OrthogonalEuclidean OrthogonalMaps AdjointCriteria
  EuclideanLebesgueLinear EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_dimension_projection_orthogonal]: supporting
    identification of O*(n,n) with O(n)
    used in 2.10.35, p. 197,
    from 1.7.2 and 1.7.4, pp. 28–31. *)
Lemma equal_dimension_projection_orthogonal (R : realType) (n : nat)
    (p : {linear R_n R n -> R_n R n}) :
  O_star p -> is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) p.
Proof.
move=> [f [hf ha]].
have [g [hg [hfg hgf]]] := @FedererOrthogonal.O_inverse R n f hf.
have hfp := proj1 (orthogonal_iff_adjoint_left_inverse (@euclidean_inner_productP R n) ha) hf.
have he : p =1 g by move=> x; rewrite -(hgf x) hfp.
by move=> x y; rewrite !he hg.
Qed.

(** Source for [equal_dimension_projection_volume]: supporting
    L^n[p(S)]=L^n(S) for O*(n,n)
    in 2.10.35, p. 197. The
    equality holds on arbitrary sets, without
    Borel or finite-measure hypotheses. *)
Theorem equal_dimension_projection_volume (R : realType) (n : nat)
    (p : {linear R_n R n -> R_n R n})
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  O_star p -> euclidean_lebesgue_measure n (p @` S)=euclidean_lebesgue_measure n S.
Proof.
move=> hp; have ho := equal_dimension_projection_orthogonal hp.
have hinj : injective p := orthogonal_map_injective (@euclidean_inner_productP R n) (@euclidean_inner_productP R n) ho.
have he : p @^-1` (p @` S)=S.
  apply/seteqP; split=> x hx; last by exists x.
  have [y hy hxy] := hx; by rewrite -(hinj _ _ hxy).
have hh := @euclidean_orthogonal_pushforward R n p ho (p @` S).
by rewrite he in hh.
Qed.
