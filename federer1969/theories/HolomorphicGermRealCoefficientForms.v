(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 319: actual holomorphic germ derivatives have bounded
    real symmetric-form restrictions with exactly the same norms.
    Use the original jet, its proved symmetry and the existing
    tuple-form and continuous-multilinear norm theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  SymmetricForms SymmetricOperatorNorm MultilinearTupleForm ContinuousMultilinearSymmetricNorm
  ContinuousSymmetricFormAdapter ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermJetSymmetry HolomorphicGermGrowthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Forms.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o).
Variable NX:XR->R.
Variable hNX:is_real_norm NX.
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m XR CR NX N hNX hN).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m XR CR NX N hNX hN).
Local Notation NZ:=(fun m=>@ContinuousMultilinear.norm R m XR CR NX N hNX hN).
Local Notation hZ:=(fun m=>@ContinuousMultilinear.laws R m XR CR NX N hNX hN).

(** Source for [holomorphic_germ_coefficient_forms_exists]: the actual
    restricted real forms and their exact original jet norms,
    extending 3.4.5, p. 319. Selected forms remain local
    existence witnesses; the original germ and jets stay opaque. *)
Theorem holomorphic_germ_coefficient_forms_exists a (alpha:holomorphic_germ_space hNX a):
  exists phi:forall m,S_m XR CR m,
    (forall m u,phi m u=ev m [ffun i=>tnth u i] (@HolomorphicGermJets.value R X NX hNX a m alpha)) /\
    (forall m,@norm_bounded_symmetric_form R m XR CR NX N (phi m)) /\
    forall m,@symmetric_operator_norm R XR CR NX hNX.1 N m (phi m)=
      (@holomorphic_germ_jet_norm R X NX hNX a m alpha)%:E.
Proof.
pose w m:=@HolomorphicGermJets.value R X NX hNX a m alpha.
have hex m:exists phi:S_m XR CR m,forall u,phi u=ev m [ffun i=>tnth u i] (w m).
  exact:(@symmetric_multilinear_tuple_form_exists R XR CR m (fun u=>ev m u (w m))
    (continuous_multilinear_evaluation (hZ m) (w m)) (@holomorphic_germ_jet_symmetric R X NX hNX a m alpha)).
pose phi m:=projT1 (cid (hex m)).
have hPhi m:=projT2 (cid (hex m)).
have hNorm m:@symmetric_operator_norm R XR CR NX hNX.1 N m (phi m)=(NZ m (w m))%:E.
  exact:(@continuous_multilinear_symmetric_norm R m XR CR (Z m) NX N hNX hN
    (ev m) (NZ m) (hZ m) (w m) (phi m) (hPhi m)).
exists phi;split;first exact:hPhi.
split;last exact:hNorm.
move=>m;apply:(@finite_operator_norm_sform_bounded R m XR CR NX N hNX hN (phi m) (NZ m (w m))).
by rewrite hNorm.
Qed.
End Forms.
