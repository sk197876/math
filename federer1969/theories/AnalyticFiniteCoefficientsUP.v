(** Supporting Federer (1969), 3.4.8(5), p. 328:
    original finite Taylor coefficients with the multiindex
    factorial of 1.9.3, p. 42. State the value law before
    existence or sealing; no dimension or ideal law is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed AnalyticGermRing
  AnalyticGermJetsSealed SymmetricMultiIndices SymmetricIndexBounds SymmetricDividedMonomials
  SymmetricMonomialTuples FiniteJetDegreeIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_jet_monomial_arguments]: the original
    repeated basis arguments of 1.10.5, p. 48, supporting finite
    Taylor coefficients in Federer 3.4.8(5), p. 328. *)
Definition finite_jet_monomial_arguments (R:realType) (X:lmodType R) n
    (e:'I_n->X) l (j:finite_jet_degree_indices n l):{ffun 'I_(tag j)->X}:=
  [ffun i=>tnth (symmetric_monomial_tuple e (tagged j)) i].

(** Source for [is_analytic_finite_coefficient_map]: supporting
    coefficient specification for Federer 3.4.8(5), p. 328. Every
    value is the actual original derivative on its repeated basis
    arguments divided by alpha!, as in 1.9.3 and 1.10.5. The laws
    supply neither injectivity, surjectivity nor an ideal-power kernel. *)
Definition is_analytic_finite_coefficient_map (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) l a
    (f:@analytic_germ_ring R X NX hNX a->{ffun finite_jet_degree_indices n l->R^o}):Prop:=
  forall alpha j,f alpha j =
    ((symmetric_multi_factorial (finite_jet_degree_multiindex j))%:R:R)^-1 *
      @ContinuousMultilinear.evaluation R (tag j) X R^o NX (fun z=>`|z|)
        hNX (@scalar_absolute_value_norm R) (finite_jet_monomial_arguments e j)
        (@AnalyticGermJets.value R X NX hNX a (tag j) alpha).
