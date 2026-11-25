(** Federer (1969), 2.5.10, pp. 100–101: representation of bounded L1
    functionals under the disjoint finite-measure decomposition condition.
    The density is not required to have countably measurable support. This
    is the decomposition corollary within 2.5.10; the continuum- hypothesis
    discussion, geometric example, and Radon corollary are separate
    assertions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureAlmostUP MeasureAlmostBasic
  FunctionLatticeSeminormUP FunctionOperatorSeminorm TotalScalarLpUP TotalScalarLpLattice
  TotalScalarLpFiniteSeminorm TotalScalarPairingValue TotalEssentialNormBound RealLatticeDensityUP
  FiniteMeasureDecompositionUP DisjointLocalDensity BoundedMeasurablePairing
  CutoffFunctionalAgreement LoneFunctionalLocalDetermination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_lone_density_from_finite_decomposition]: the
    disjoint-decomposition representation assertion of Federer 2.5.10, pp.
    100–101 The proof supplies the uniform pointwise bound on the selected
    density and actual finite integrals on every total L1 test. *)
Theorem bounded_lone_density_from_finite_decomposition (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (B : J -> set X)
    (A : (X -> R) -> R) (M : R) :
  is_finite_measure_decomposition mu D B -> (0 <= M)%R ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  (forall f, total_scalar_lp mu 1 f -> (`|A f| <= M * finite_total_scalar_lp_norm mu 1 f)%R) ->
  exists k : X -> R, is_real_lattice_density mu (total_scalar_lp mu 1) A k /\
    forall x, (`|k x| <= M)%R.
Proof.
move=> hD hM hA hb.
have [k [hk [hbound hlocal]]] := @disjoint_local_density_exists R X J mu hm D B A M hD hM hA hb.
have [hC hpair] := @bounded_measurable_pairing_linear_bound R X mu hm k M hM hk hbound.
have he : forall f, total_scalar_lp mu 1 f -> A f=total_scalar_pairing mu f k.
  apply: (@lone_functionals_determined_on_finite_pieces R X J mu hm D B A
    (fun f => total_scalar_pairing mu f k) M M hD.2.2 (fun j hj => (hD.1 j hj).1)
    hM hM hA hC hb (fun f hf => (hpair f hf).2)).
  move=> j hj f hf; symmetry; exact: total_scalar_pairing_value_of_integral (hlocal j hj f hf).
exists k; split=> //; split=> // f hf.
have hi := (hpair f hf).1; by rewrite -(he f hf) in hi.
Qed.

(** Source for [lone_functional_representation_by_finite_decomposition]:
    bounded-functional formulation of the same assertion in Federer 2.5.10,
    pp. 100–101 The closed-unit-ball norm is the corrected 2.5.7 convention,
    erratum p. 2, book p. 98 line 11. The conclusion includes an essential
    bound without imposing full L-infinity membership. *)
Theorem lone_functional_representation_by_finite_decomposition (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (B : J -> set X)
    (A : (X -> R) -> R) :
  is_finite_measure_decomposition mu D B ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  function_operator_seminorm (total_scalar_lp mu 1) A (finite_total_scalar_lp_norm mu 1) < +oo ->
  exists k : X -> R, is_real_lattice_density mu (total_scalar_lp mu 1) A k /\
    total_scalar_lp_norm mu +oo k <= function_operator_seminorm (total_scalar_lp mu 1) A (finite_total_scalar_lp_norm mu 1).
Proof.
move=> hD hA hfin.
have [M [hMnorm [hM hb]]] := @function_operator_seminorm_finite_bound R X _ A _
  (@total_scalar_lp_vector_lattice R X mu hm 1 (lexx _)) hA
  (@finite_total_scalar_lp_norm_laws R X mu hm 1) hfin.
have [k [hk hbound]] := @bounded_lone_density_from_finite_decomposition R X J mu hm D B A M hD hM hA hb.
exists k; split=> //; rewrite hMnorm; apply: (@total_essential_norm_bound R X mu hm k M hM).
apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
exact: hbound.
Qed.
