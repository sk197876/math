(** Federer (1969), 1.8.1, p. 38: compactness of S, the simple unit ball. We
    use all unit-ball factor tuples, whose image is still exactly S, as
    explained in SimpleUnitFactors.v. Only general product/image compactness
    and the project's finite-dimensional compactness are used. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  InnerExteriorPositivity InnerBoundedness InnerFiniteCompactness
  SimpleUnitBall SimpleUnitFactors ExteriorProductContinuity
  ExteriorGrading FiniteExteriorPowers LinearBasis GramSchmidt OrthonormalisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simple_unit_ball_compact]: Federer 1.8.1, p. 38, the
    displayed simple unit ball S is compact Positive degree is explicit, and
    degrees above the ambient dimension are included. *)
Theorem simple_unit_ball_compact (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m)%N) :
  compact (@simple_unit_ball R h2 V B hB m :
    set (inner_metric_space (@exterior_inner_productP R h2 V B hB m))).
Proof.
pose M := inner_metric_space hB.
pose E := inner_metric_space (@exterior_inner_productP R h2 V B hB m).
pose A : set ('I_m -> M) := fun u => forall i, inner_norm hB (u i) <= 1.
pose f (u : 'I_m -> M) : E := @e_lambda R (Choice.clone 'I_m _) V u m (ord_tuple m).
have hball : compact (@inner_unit_ball R V B hB).
  apply: inner_unit_ball_compact; exact: inner_finite_basis_boundedly_compact he.
have hA : compact A.
  exact (@tychonoff _ (fun _ : 'I_m => (Topological.clone M _))
    (fun _ => @inner_unit_ball R V B hB) (fun _ => hball)).
have hf : continuous f.
  have [d [hd hdo]] := orthonormal_basis_exists hB he.
  exact (@exterior_product_continuous_orthonormal R h2 V B hB n d hd (orthonormalisation_orthonormal hdo) m).
have heq : @simple_unit_ball R h2 V B hB m = f @` A.
  apply: funext => x; apply: propext; split.
  - move=> hx; have [u [hu hux]] := simple_unit_ball_factors hm hx.
    exists u => //; exact: esym hux.
  - move=> [u hu <-]; exact: unit_factors_simple_unit_ball hu.
rewrite heq; apply: continuous_compact hA; exact: continuous_subspaceT hf.
Qed.
