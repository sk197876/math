(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2),(5),
    pp. 326, 328: actual unitary transformations induce
    continuous homomorphisms of the original holomorphic germ ring.
    The unitary norm equation proves holomorphy. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals topology.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupHaarMeasure UnitaryGroup UnitaryComplexMapSealed HolomorphicAtUP HolomorphicUP
  HolomorphicLinear NormDifferentialUP NormOpenDomainLaws HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermMetric PointedHolomorphicPullbackUP PointedHolomorphicPullbackSealed
  PointedHolomorphicPullbackRingMorphism PointedHolomorphicPullbackContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Pullback.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable N:nat.
Variable e:'I_N->restricted_space (ComplexScalars.embed R) X.
Variable he:is_basis e.
Local Notation U:=(@unitary_group R X H hH N e he).
Local Notation NX:=(inner_norm (hermitian_real_inner_product hH)).
Local Notation hNX:=(complex_norm_real (hermitian_complex_norm hH)).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation mapg:=(fun g:U=>@UnitaryComplexMap.value R X H hH N e he g).

(** Source for [unitary_germ_coordinate_holomorphic]: an original
    unitary map is holomorphic at zero, 3.4.12, p. 339. *)
Lemma unitary_germ_coordinate_holomorphic (g:U):
  @is_holomorphic_at R X X NX NX hNX hNX setT (mapg g) 0.
Proof.
have hBound:norm_bounded_linear NX NX (complex_hom_real (mapg g)).
  exists 1;split;first exact:ler01.
  move=>x;rewrite complex_hom_real_values (@UnitaryComplexMap.laws R X H hH N e he g)
    (@unitary_element_norm R X H hH N e he g) mul1r.
  exact:lexx.
exists setT;split;first exact:Logic.I.
split;first by move=>x _.
exact:(@holomorphic_bounded_linear R X X NX NX hNX hNX setT (mapg g)
  (fun x _=>@norm_full_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX x) hBound).
Qed.

(** Source for [holomorphic_unitary_germ_map]: actual O^C_0(g),
    used in the original rotated ideals, 3.4.12, p. 339. *)
Definition holomorphic_unitary_germ_map (g:U):{rmorphism G->G}:=
  @pointed_holomorphic_germ_ring_pullback R X X NX NX hNX hNX (mapg g) 0 0
    (@PointedHolomorphicPullback.map R X X NX NX hNX hNX setT (mapg g) 0 0
      (unitary_germ_coordinate_holomorphic g) (linear0 (mapg g)))
    (@PointedHolomorphicPullback.laws R X X NX NX hNX hNX setT (mapg g) 0 0
      (unitary_germ_coordinate_holomorphic g) (linear0 (mapg g))).

(** Source for [holomorphic_unitary_germ_map_specification]: every
    original representative composes with the actual unitary map,
    3.4.12, p. 339. *)
Lemma holomorphic_unitary_germ_map_specification (g:U):
  is_pointed_holomorphic_germ_pullback (mapg g) (holomorphic_unitary_germ_map g).
Proof.
exact:(@PointedHolomorphicPullback.laws R X X NX NX hNX hNX setT (mapg g) 0 0
  (unitary_germ_coordinate_holomorphic g) (linear0 (mapg g))).
Qed.

(** Source for [holomorphic_unitary_germ_map_continuous]: original
    unitary pullback is continuous in the exact derivative metric,
    extending 3.4.8(5), p. 328, under 3.4.12, p. 339. *)
Lemma holomorphic_unitary_germ_map_continuous (g:U):
  continuous (fun alpha:@holomorphic_germ_metric R X NX hNX 0=>
    (holomorphic_unitary_germ_map g alpha:@holomorphic_germ_metric R X NX hNX 0)).
Proof.
exact:(@pointed_holomorphic_germ_pullback_continuous R X X NX NX hNX hNX setT (mapg g) 0 0
  (holomorphic_unitary_germ_map g) (unitary_germ_coordinate_holomorphic g)
  (linear0 (mapg g)) (holomorphic_unitary_germ_map_specification g)).
Qed.
End Pullback.
