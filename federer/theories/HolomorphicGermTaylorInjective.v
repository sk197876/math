(** Federer (1969), 3.4.12, p. 339: the original complex
    germ is determined by its actual derivatives. Apply the
    normed-target Taylor equality theorem and the original local
    germ quotient laws; no formal series carrier replaces the germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormMetric ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormHigherDifferentialUnique NormAnalyticUP NormAnalyticDomain NormAnalyticTaylorEquality
  LocalGermUP LocalGermSealed HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRingLaws HolomorphicGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Germs.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Variable NX:XR->R.
Variable hNX:is_real_norm NX.
Variable a:X.
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m XR CR NX N hNX hN).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m XR CR NX N hNX hN).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m XR CR NX N hNX hN).
Local Notation hZ:=(fun m=>@ContinuousMultilinear.laws R m XR CR NX N hNX hN).

(** Source for [holomorphic_germ_jets_injective]: the actual jet
    separation needed in the complex extension of 3.4.6,
    p. 323, as required by 3.4.12, p. 339. *)
Theorem holomorphic_germ_jets_injective (alpha beta:holomorphic_germ_space hNX a):
  (forall m,@HolomorphicGermJets.value R X NX hNX a m alpha=
    @HolomorphicGermJets.value R X NX hNX a m beta) ->alpha=beta.
Proof.
move=>hJets.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
have [g hg]:=@holomorphic_germ_has_representative R X NX hNX a beta.
have [A [ha hF]]:=holomorphic_representative_holomorphic f.
have [B [hb hG]]:=holomorphic_representative_holomorphic g.
have hFA:=@norm_analytic_at_domain_enlargement R XR CR NX N hNX hN A setT
  (holomorphic_representative_value f) a (fun x _=>Logic.I) (hF.1 a ha).
have hGA:=@norm_analytic_at_domain_enlargement R XR CR NX N hNX hN B setT
  (holomorphic_representative_value g) a (fun x _=>Logic.I) (hG.1 a hb).
have hEqual m (z w:Z m):has_norm_higher_differential NX ev ZN setT
    (holomorphic_representative_value f) m a z ->
    has_norm_higher_differential NX ev ZN setT (holomorphic_representative_value g) m a w ->z=w.
  move=>hz hw.
  have hZEq:=norm_higher_differential_unique hNX hN hZ hz
    (@HolomorphicGermJets.laws R X NX hNX a m alpha f hf).
  have hWEq:=norm_higher_differential_unique hNX hN hZ hw
    (@HolomorphicGermJets.laws R X NX hNX a m beta g hg).
  by rewrite hZEq hWEq hJets.
have [U [hU [haU hValues]]]:=@norm_analytic_equal_jets_local R XR CR NX N hNX hN
  (holomorphic_representative_value f) (holomorphic_representative_value g) a hFA hGA hEqual.
rewrite -hf -hg;apply/(local_germ_equality (@LocalGerms.laws
  (Topological.clone (real_norm_metric_space hNX) _) C
  (@holomorphic_representative_type R X NX hNX a)
  (@holomorphic_representative_value R X NX hNX a) a)).
by exists U.
Qed.
End Germs.
