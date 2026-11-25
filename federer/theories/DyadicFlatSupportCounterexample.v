(** Federer (1969), 4.1.12, p. 368: the
    original dyadic interval-series boundary is a
    flat zero-chain, but is not flat
    with its own support as compact index.
    Its support carries no nonzero normal
    one-current; the flat and mass closures
    there coincide, while its mass is infinite. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentSupportGeometry
  SmoothCompactSet CurrentMassSealed NormalCurrentsUP FlatCurrentsUP FlatCurrentMassNoFillings
  CurrentNormalMassClosure CurrentFlatMassClosureEquality ScalarCurrentIntervalCompact
  DyadicCurrentEndpointCompact DyadicIntervalCurrentLaws DyadicIntervalBoundarySupport DyadicIntervalBoundaryMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DyadicFlatSupportCounterexample.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation T := (@dyadic_interval_boundary R h2).
Local Notation support d := (@current_support R h2 1%N Full hFull d).

(** Source for [dyadic_interval_boundary_support_index]:
    the actual support of the original T,
    used as the compact index in
    Federer 4.1.12, p. 368. The
    compactness proof uses its proved containment
    in the literal compact endpoint set. *)
Definition dyadic_interval_boundary_support_index:smooth_compact_set hNX Full:=
  @Build_smooth_compact_set R X NX hNX Full (support 0%N T) (fun x hx=>hx.1)
    (@current_support_compact_bound R h2 1%N 0%N Full hFull
      (dyadic_current_endpoint_compact R) T (@dyadic_interval_boundary_support R h2)).
Local Notation K := dyadic_interval_boundary_support_index.

(** Source for [dyadic_interval_boundary_support_no_normal_filling]:
    the original support of T contains no
    support of a nonzero normal one-current,
    exactly the assertion in Federer 4.1.12,
    p. 368. This follows from its
    actual dyadic geometry, without awaiting the
    general regularisation theorem of 4.1.18. *)
Theorem dyadic_interval_boundary_support_no_normal_filling
    (S:@current_space R h2 1%N Full hFull 1%N):
  @is_normal_current R h2 1%N Full hFull 1%N S->
  support 1%N S `<=` smooth_compact_carrier K->S=0.
Proof.
move=>hNormal hSupport.
apply:(@dyadic_endpoint_normal_one_current_zero R h2 S hNormal)=>x hx.
exact:(@dyadic_interval_boundary_support R h2 x (hSupport x hx)).
Qed.

(** Source for [dyadic_interval_boundary_support_closures_equal]:
    F_(0,spt T)(R) equals the mass
    closure of N_(0,spt T)(R), the
    original assertion in Federer 4.1.12,
    p. 368. Every candidate current is
    retained, without an extra support or
    finite-mass premise. *)
Theorem dyadic_interval_boundary_support_closures_equal
    (Q:@current_space R h2 1%N Full hFull 0%N):
  @is_flat_current_supported_in R h2 1%N 0%N Full hFull K Q<->
  @is_normal_current_mass_closure R h2 1%N 0%N Full hFull K Q.
Proof.
exact:(@current_flat_mass_closures_equal_no_fillings R h2 1%N 0%N Full hFull K
  dyadic_interval_boundary_support_no_normal_filling Q).
Qed.

(** Source for [dyadic_interval_boundary_not_flat_on_own_support]:
    the original T is not in
    F_(0,spt T)(R), as asserted in
    Federer 4.1.12, p. 368. The
    infinite mass contradicts the preceding actual
    finite-mass consequence for that exact compact index. *)
Theorem dyadic_interval_boundary_not_flat_on_own_support:
  ~@is_flat_current_supported_in R h2 1%N 0%N Full hFull K T.
Proof.
move=>hFlat.
have[_ hFinite]:=@flat_current_mass_equals_flat_no_fillings R h2 1%N 0%N Full hFull K
  dyadic_interval_boundary_support_no_normal_filling T hFlat.
by rewrite (@dyadic_interval_boundary_infinite_mass R h2) ltxx in hFinite.
Qed.

(** Source for [dyadic_interval_boundary_is_flat]:
    the same actual T belongs to
    F_0(R), the original contrasting membership
    in Federer 4.1.12, p. 368. *)
Theorem dyadic_interval_boundary_is_flat:@is_flat_current R h2 1%N 0%N Full hFull T.
Proof.
exists (scalar_current_compact_interval R 0 (1/2));exact:dyadic_interval_boundary_flat.
Qed.
End DyadicFlatSupportCounterexample.
