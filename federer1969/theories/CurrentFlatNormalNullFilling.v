(** Federer (1969), 4.1.12, p. 368: when
    K supports no nonzero normal filling, the
    flat norm of each finite-mass current supported
    in K equals its mass. Apply the preceding
    normal-minimiser parenthesis, retaining its finite-mass premise. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary SmoothCompactSet
  CurrentFlatNorm CurrentFlatMinimum CurrentMassSealed CurrentMassFiniteAlgebra NormalCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_flat_equals_mass_no_normal_fillings]:
    F_K(T)=M(T) for finite-mass T supported in K
    if K supports no nonzero normal (m+1)-current.
    This is the original normal-filling argument in
    Federer 4.1.12, p. 368, before passage to
    the two closures. Infinite-mass currents are not
    covered by the normal-minimiser parenthesis alone. *)
Theorem current_flat_equals_mass_no_normal_fillings (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hNoFilling:forall S:@current_space R h2 n U hU m.+1,
      @is_normal_current R h2 n U hU m.+1 S->
      @current_support R h2 n U hU m.+1 S `<=` smooth_compact_carrier K->S=0)
    (T:@current_space R h2 n U hU m):
  @current_support R h2 n U hU m T `<=` smooth_compact_carrier K->
  (@CurrentMass.value R h2 n m U hU T< +oo)%E->
  @current_flat_norm R h2 n m U hU K T=@CurrentMass.value R h2 n m U hU T.
Proof.
move=>hSupport hFinite.
have[S [hNormal [hS [hValue hLeast]]]]:=
  @current_flat_minimum_normal_filling R h2 n m U hU K T hSupport hFinite.
have hZero:S=0:=hNoFilling S hNormal hS.
by rewrite hZero linear0 subr0 current_mass_zero adde0 in hValue.
Qed.
