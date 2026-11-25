(** Federer (1969), 1.8.1, p. 38, compactness of the set S: supporting
    continuity of the exterior product on finite tuples. The proof expands
    in finite coordinates using the project's exterior algebra laws and
    general topological rules for finite sums, products, and scalar
    multiplication. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology
  InnerExteriorPositivity InnerFiniteSynthesis InnerCoordinateContinuity
  ExteriorAlgebra ExteriorGrading ExteriorExpansion FiniteExteriorPowers GradedComponents
  OrthonormalFamilies LinearBasis GramSchmidt OrthonormalisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Section Continuity.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Hypothesis ho : orthonormal_family B e.
Variable m : nat.
Local Notation M := (inner_metric_space hB).
Local Notation E := (inner_metric_space (@exterior_inner_productP R h2 V B hB m)).

(** Source for [exterior_product_coordinate_expansion]: Federer
    1.8.1, p. 38, supporting finite polynomial expression used for
    compactness of S. The algebraic expansion is that of 1.3.4, p. 16. *)
Lemma exterior_product_coordinate_expansion (u : 'I_m -> M) :
  @e_lambda R (Choice.clone 'I_m _) V u m (ord_tuple m) =
    \sum_(f : {ffun 'I_m -> 'I_n})
      (\prod_i inner_coordinate hB (e (f i)) (u i)) *:
      e_lambda (fun i => e (f i)) (ord_tuple m).
Proof.
have hu i : u i = \sum_j inner_coordinate hB (e j) (u i) *: e j.
  exact: esym (@inner_finite_synthesis_coordinates R V B hB n e he ho (u i)).
apply: val_inj.
change (component_val (@e_lambda R (Choice.clone 'I_m _) V u m (ord_tuple m)) = component_val
  (\sum_(f : {ffun 'I_m -> 'I_n})
    (\prod_i inner_coordinate hB (e (f i)) (u i)) *:
    e_lambda (fun i => e (f i)) (ord_tuple m))).
rewrite e_lambdaE linear_sum.
rewrite (eq_map hu) exterior_word_expansion.
apply: eq_bigr => f _; by rewrite linearZ ?e_lambdaE.
Qed.

(** Source for [exterior_product_continuous_orthonormal]: Federer 1.8.1, p.
    38, supporting continuity of the natural product map An orthonormal
    coordinate proof. *)
Theorem exterior_product_continuous_orthonormal :
  continuous (fun u : 'I_m -> M => (@e_lambda R (Choice.clone 'I_m _) V u m (ord_tuple m) : E)).
Proof.
have hf : (fun u : 'I_m -> M => (@e_lambda R (Choice.clone 'I_m _) V u m (ord_tuple m) : E)) =
    (fun u : 'I_m -> M =>
      \sum_(f : {ffun 'I_m -> 'I_n})
        (\prod_i inner_coordinate hB (e (f i)) (u i)) *:
        (e_lambda (fun i => e (f i)) (ord_tuple m) : E)).
  apply: funext => u; exact: exterior_product_coordinate_expansion.
rewrite hf; apply: continuous_big; first exact: add_continuous.
move=> f _ u; apply: continuousZ; last exact: cst_continuous.
apply: continuous_big; first exact: mul_continuous.
move=> i _ v.
apply: (@continuous_comp (Topological.clone ('I_m -> M) _)
  (Topological.clone M _) (Topological.clone R^o _)
  (fun v => v i) (inner_coordinate hB (e (f i))) v).
- exact: proj_continuous.
- exact: inner_coordinate_continuous.
Qed.
End Continuity.
