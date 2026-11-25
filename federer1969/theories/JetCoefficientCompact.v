(** Federer (1969), 3.4.5, p. 319: bounded
    symmetric derivative sequences lie in a compact coefficient set.
    Only the general-topology product compactness theorem is used
    as background; finite-dimensional coefficient compactness is proved
    from the project's existing basis and norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology fingroup perm.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm FiniteArgumentPermutation FiniteMultilinearCompact JetSymmetryClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coefficients.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m X R^o NX NS hNX hNS).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m X R^o NX NS hNX hNS).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m X R^o NX NS hNX hNS).
Local Notation hZ:=(fun m=>@ContinuousMultilinear.laws R m X R^o NX NS hNX hNS).
Local Notation hZN:=(fun m=>continuous_multilinear_norm_is_norm hNS (hZ m)).
Local Notation T:=(fun m=>Topological.clone (real_norm_metric_space (hZN m)) _).

(** Source for [bounded_symmetric_jet_coefficients_compact]:
    coefficient compactness in 3.4.5, p. 319.
    Actual coefficient norm balls are compact in every order.
    Their product is compact, and the actual permutation
    equations define a closed subset. No analytic realisation
    or compactness of the germ growth class is assumed here. *)
Theorem bounded_symmetric_jet_coefficients_compact (s t:nat):
  @compact (prod_topology T)
    [set w:prod_topology T|
      (forall m,ZN m (w m)<=s%:R*t%:R^+m*(m`!)%:R) /\
      forall m (sigma:'S_m) (u:{ffun 'I_m->X}),
        ev m (finite_argument_permutation sigma u) (w m)=ev m u (w m)].
Proof.
pose K:set (prod_topology T):=fun w=>forall m,ZN m (w m)<=s%:R*t%:R^+m*(m`!)%:R.
have hCompact:compact K.
  exact:(@tychonoff nat T
    (fun m=>[set z:T m|ZN m z<=s%:R*t%:R^+m*(m`!)%:R])
    (fun m=>@finite_scalar_derivative_ball_compact R X NX hNX n b hb m _)).
pose C:set (prod_topology T):=fun w=>forall m (sigma:'S_m) (u:{ffun 'I_m->X}),
  ev m (finite_argument_permutation sigma u) (w m)=ev m u (w m).
have hClosed:closed C.
  apply:(@jet_symmetry_locus_closed R X NX hNX (prod_topology T) (fun m w=>w m)).
  move=>m;exact:proj_continuous.
change (compact (K `&` C)).
exact:compact_closedI hCompact hClosed.
Qed.
End Coefficients.
