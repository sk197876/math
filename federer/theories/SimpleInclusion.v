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
  SimpleProducts AssociatedFiniteFamily AssociatedFactorInclusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, fourth corollary: T_xi is contained in T_eta
    exactly when eta=xi wedge zeta with zeta of degree n-m. The forward
    implication follows by applying the preceding factorisation to the
    actual factors of xi. *)
Section Inclusion.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables m n : nat.
Variables (xi : exterior_power V m) (eta : exterior_power V n).
Hypotheses (hxi : xi != 0) (heta : eta != 0) (sxi : simple xi) (seta : simple eta).
(** Source for [simple_associated_inclusion]: Federer (1969), 1.6.1, p. 24,
    fourth corollary. In words: Inclusion of associated spaces of nonzero
    simple vectors is equivalent to factoring the larger-degree vector by
    the smaller-degree vector with a factor of the complementary degree.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. Follow the stated factorisation eta = xi wedge zeta. *)
Theorem simple_associated_inclusion :
  (forall v, FedererSimple.T xi v -> FedererSimple.T eta v) <->
  exists zeta : exterior_power V (n-m),
    component_val eta = wedge (component_val xi) (component_val zeta).
Proof.
split.
- move=> ht; have [t hxt] := sxi; rewrite tuple_product in hxt.
  pose e := tnth t.
  have hxw : exterior_word [seq e i | i <- enum 'I_m] != 0.
    apply/eqP=> hz; apply: (elimT negP hxi); apply/eqP; rewrite hxt; apply: val_inj.
    change (component_val (e_lambda e (ord_tuple m)) = component_val (0 : exterior_power V m)).
    by rewrite e_lambdaE linear0.
  have he := nonzero_word_independent hxw.
  have heT i : FedererSimple.T eta (e i).
    apply: ht; rewrite hxt; exact: product_associated_generator.
  have [_ [zeta hz]] := @associated_finite_family K h2 V n m eta e he heT heta.
  exists zeta; by rewrite hxt.
- move=> [zeta hz]; exact: associated_factor_inclusion hz.
Qed.
(** Source for [simple_inclusion_dimension]: Federer (1969), 1.6.1, p. 24,
    fourth corollary. In words: Inclusion of associated spaces of nonzero
    simple vectors is equivalent to factoring the larger-degree vector by
    the smaller-degree vector with a factor of the complementary degree.
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. Follow the stated factorisation eta = xi wedge zeta. *)
Theorem simple_inclusion_dimension :
  (forall v, FedererSimple.T xi v -> FedererSimple.T eta v) -> (m <= n)%N.
Proof.
move=> ht; have [t hxt] := sxi; rewrite tuple_product in hxt.
pose e := tnth t.
have hxw : exterior_word [seq e i | i <- enum 'I_m] != 0.
  apply/eqP=> hz; apply: (elimT negP hxi); apply/eqP; rewrite hxt; apply: val_inj.
  change (component_val (e_lambda e (ord_tuple m)) = component_val (0 : exterior_power V m)).
  by rewrite e_lambdaE linear0.
have he := nonzero_word_independent hxw.
have heT i : FedererSimple.T eta (e i).
  apply: ht; rewrite hxt; exact: product_associated_generator.
exact (proj1 (@associated_finite_family K h2 V n m eta e he heT heta)).
Qed.
End Inclusion.
