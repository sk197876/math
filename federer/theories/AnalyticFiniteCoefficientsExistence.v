(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the actual derivative evaluations give the independently
    specified finite Taylor coefficients. This construction proves
    existence only; downstream statements use the sealed value law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed AnalyticGermRing
  AnalyticGermJetsSealed SymmetricDividedMonomials FiniteJetDegreeIndices AnalyticFiniteCoefficientsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_finite_coefficient_map_exists]: supporting
    existence of the exact original finite Taylor coefficients for
    Federer 3.4.8(5), p. 328, including degree zero and empty prefixes. *)
Theorem analytic_finite_coefficient_map_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) l a:
  exists f:@analytic_germ_ring R X NX hNX a->{ffun finite_jet_degree_indices n l->R^o},
    is_analytic_finite_coefficient_map e f.
Proof.
exists (fun alpha=>[ffun j:finite_jet_degree_indices n l=>
  ((symmetric_multi_factorial (finite_jet_degree_multiindex j))%:R:R)^-1 *
    @ContinuousMultilinear.evaluation R (tag j) X R^o NX (fun z=>`|z|)
      hNX (@scalar_absolute_value_norm R) (finite_jet_monomial_arguments e j)
      (@AnalyticGermJets.value R X NX hNX a (tag j) alpha)]).
by move=>alpha j;rewrite ffunE.
Qed.

(** Source for [analytic_finite_coefficient_map_unique]: the exact
    original coefficient values determine the map, supporting Federer
    3.4.8(5), p. 328. No selected representative is exposed. *)
Lemma analytic_finite_coefficient_map_unique (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) l a
    (f g:@analytic_germ_ring R X NX hNX a->{ffun finite_jet_degree_indices n l->R^o}):
  is_analytic_finite_coefficient_map e f ->is_analytic_finite_coefficient_map e g ->f = g.
Proof.
move=>hF hG;apply:funext=>alpha;apply/ffunP=>j;by rewrite hF hG.
Qed.
