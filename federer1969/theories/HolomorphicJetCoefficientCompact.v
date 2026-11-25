(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 319: the original complex symmetric coefficients with
    factorial bounds form a compact set. Reuse actual finite
    derivative balls, product compactness and the proved closed
    symmetry and complex scalar equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology fingroup perm.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  NormMetric LinearBasis ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  ComplexScalarSlotUP ComplexMultilinearSlotsClosed FiniteArgumentPermutation
  FiniteComplexMultilinearCompact NormJetSymmetryClosed HolomorphicFormalJetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coefficients.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:is_complex_norm NX.
Local Notation C:=(ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m XR CR NX N hNXR hN).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m XR CR NX N hNXR hN).
Local Notation NZ:=(fun m=>@ContinuousMultilinear.norm R m XR CR NX N hNXR hN).
Local Notation hZ:=(fun m=>@ContinuousMultilinear.laws R m XR CR NX N hNXR hN).
Local Notation hNZ:=(fun m=>continuous_multilinear_norm_is_norm hN (hZ m)).
Local Notation T:=(fun m=>Topological.clone (real_norm_metric_space (hNZ m)) _).
Variable n:nat.
Variable b:'I_n->XR.
Variable hb:is_basis b.

(** Source for [bounded_holomorphic_jet_coefficients_compact]: actual
    complex coefficient compactness underlying the original growth
    classes, extending 3.4.5, p. 319. Compactness and
    realisation are not coefficient hypotheses. *)
Theorem bounded_holomorphic_jet_coefficients_compact (s t:nat):
  @compact (prod_topology T)
    [set w:prod_topology T|@is_holomorphic_formal_jet R X NX hNX s t w].
Proof.
pose P:=prod_topology T.
pose K:set P:=fun w=>forall m,NZ m (w m)<=s%:R*t%:R^+m*(m`!)%:R.
have hK:compact K.
  exact:(@tychonoff nat T (fun m=>[set z:T m|NZ m z<=s%:R*t%:R^+m*(m`!)%:R])
    (fun m=>@finite_complex_derivative_ball_compact R XR NX hNXR n b hb m _)).
pose S:set P:=fun w=>forall m (sigma:'S_m) u,ev m (finite_argument_permutation sigma u) (w m)=ev m u (w m).
have hS:closed S.
  apply:(@norm_jet_symmetry_locus_closed R XR CR N hN NX hNXR P (fun m w=>w m)).
  move=>m;exact:proj_continuous.
pose L:set P:=fun w=>forall m,has_complex_scalar_slot_laws (fun u=>ev m u (w m)).
have hL:closed L.
  have hEquation:L=\bigcap_(m in [set:nat])
      [set w:P|has_complex_scalar_slot_laws (fun u=>ev m u (w m))].
    apply/seteqP;split=>w hw;[by move=>m _;exact:hw m|by move=>m;exact:hw m Logic.I].
  rewrite hEquation;apply:closed_bigI=>m _.
  have hSlots:=@complex_multilinear_slots_closed R X C^o NX N hNX
    (@complex_modulus_complex_norm R) m (Z m) (ev m) (NZ m) (hZ m).
  have hProof:complex_norm_real (@complex_modulus_complex_norm R)=hN:=Prop_irrelevance _ _.
  rewrite hProof in hSlots.
  change (closed ((fun w:P=>(w m:T m)) @^-1`
    [set z:T m|@has_complex_scalar_slot_laws R X C^o m (fun u=>ev m u z)])).
  apply:preimage_closed;last exact:hSlots.
  move=>w _;exact:(@proj_continuous _ T m w).
have hEquation:[set w:P|@is_holomorphic_formal_jet R X NX hNX s t w]=(K `&` S) `&` L.
  apply/seteqP;split.
  - move=>w hw;split.
    + split;[exact:holomorphic_formal_jet_growth hw|exact:holomorphic_formal_jet_symmetric hw].
    + exact:holomorphic_formal_jet_complex hw.
  - move=>w [[hGrowth hSymmetry] hComplex];by constructor.
rewrite hEquation;exact:compact_closedI (compact_closedI hK hS) hL.
Qed.
End Coefficients.
