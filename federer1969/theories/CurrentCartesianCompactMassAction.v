(** Federer (1969), 4.1.12, p. 369: supported
    finite-mass factor currents give the original product
    mass-action bound on C times D. Reuse the
    preceding product variation estimate, exact support
    law and compact mass-action bound. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianSupportUpper CurrentCartesianFiniteMassBound
  SmoothCompactSet SmoothTestSpaces SmoothFunctionTopology CurrentMassSealed CurrentCompactMassUpperAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianCompactMassAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variables (KA:smooth_compact_set hNX A) (KB:smooth_compact_set hNY B)
  (KAB:smooth_compact_set hNZ AB).
Hypothesis hKAB:smooth_compact_carrier KAB=
  @euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
Variable S:@current_space R h2 m A hA i.
Variable T:@current_space R h2 n B hB j.
Local Notation P := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T).

(** Source for [current_cartesian_compact_mass_action]:
    |(S times T)(phi)|<=M(S)M(T) nu_(C times D)^0(phi)
    for supported finite-mass factors, supporting the
    first flat product inequality of Federer 4.1.12,
    p. 369. The original compact bound is exact. *)
Theorem current_cartesian_compact_mass_action a b:
  @CurrentMass.value R h2 m i A hA S=a%:E->
  @CurrentMass.value R h2 n j B hB T=b%:E->
  @current_support R h2 m A hA i S `<=` smooth_compact_carrier KA->
  @current_support R h2 n B hB j T `<=` smooth_compact_carrier KB->
  forall phi:@current_test_space R h2 (m+n) AB hAB (i+j),
    `|@current_value R h2 (m+n) AB hAB (i+j) P phi|<=a * b *
      smooth_function_derivative_seminorm (@current_smooth_derivative_laws R h2 (m+n) AB hAB (i+j))
        KAB 0%N (smooth_test_inclusion (@current_smooth_space_laws R h2 (m+n) AB hAB (i+j)) phi).
Proof.
move=>hMassS hMassT hSupportS hSupportT phi.
have hMass:=@current_cartesian_finite_mass_bound R h2 m n i j A B hA hB S T a b hMassS hMassT.
have hSupport:@current_support R h2 (m+n) AB hAB (i+j) P `<=` smooth_compact_carrier KAB.
  move=>z hz;rewrite hKAB.
  have hFactors:=@current_cartesian_support_upper R h2 m n i j A B hA hB S T z hz.
  split;[exact:hSupportS _ hFactors.1|exact:hSupportT _ hFactors.2].
exact:(@current_compact_mass_upper_action R h2 (m+n) (i+j) AB hAB KAB P (a*b) hMass hSupport phi).
Qed.
End CurrentCartesianCompactMassAction.
