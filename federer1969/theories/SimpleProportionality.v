(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace SimpleElementary SimpleWordIndependence
  SimpleProducts FullDegreeFactor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, second corollary: equal associated subspaces of
    nonzero simple m-vectors are equivalent to proportionality by a
    nonzero scalar. The equality is extensional equality of subspaces. *)
Section Proportionality.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable m : nat.
Variables xi eta : exterior_power V m.
Hypotheses (hxi : xi != 0) (heta : eta != 0) (sxi : simple xi) (seta : simple eta).
(** Source for [simple_associated_equal]: Federer (1969), 1.6.1, p. 24,
    second corollary. In words: Two nonzero simple m-vectors have the same
    associated subspace exactly when they differ by a nonzero scalar.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem simple_associated_equal :
  (forall v, FedererSimple.T xi v <-> FedererSimple.T eta v) <->
  exists c : K, c != 0 /\ xi = c *: eta.
Proof.
split.
- move=> ht; have [t het] := seta; rewrite tuple_product in het.
  pose e := tnth t.
  have hw : exterior_word [seq e i | i <- enum 'I_m] != 0.
    apply/eqP=> hz; apply: (elimT negP heta); apply/eqP; rewrite het; apply: val_inj.
    change (component_val (e_lambda e (ord_tuple m)) = component_val (0 : exterior_power V m)).
    by rewrite e_lambdaE linear0.
  have he := nonzero_word_independent hw.
  have heT i : FedererSimple.T xi (e i).
    apply: (proj2 (ht _)); rewrite het; exact: product_associated_generator.
  have [c [hc hxc]] := @full_degree_factor K h2 V m xi e he heT hxi.
  exists c; split=> //; by rewrite het.
- move=> [c [hc ->]] v; exact (@associated_scale_nonzero K V m eta c hc v).
Qed.
End Proportionality.
