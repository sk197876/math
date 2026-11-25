(** Federer (1969), 4.1.12, p. 369: a
    zero-dimensional first factor has no boundary term.
    Its original product filling has cost
    M(S) times the second factor's decomposition cost.
    No negative-degree object is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces SmoothCompactSet
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianProductBilinear CurrentCartesianFillingBoundary
  CurrentCartesianFiniteMassBound CurrentCartesianCompactSupportBound CurrentBoundary CurrentBoundarySupport
  CurrentSupportGeometry CurrentDegreeTransport CurrentDegreeTransportSupport CurrentMassDegreeTransport
  CurrentMassSealed CurrentFiniteMassLinearBound CurrentFlatNorm CurrentFlatMassComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianFlatDecompositionZero.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n j:nat.
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
Local Notation CA d := (@current_space R h2 m A hA d).
Local Notation CB d := (@current_space R h2 n B hB d).
Local Notation MA d := (@CurrentMass.value R h2 m d A hA).
Local Notation MB d := (@CurrentMass.value R h2 n d B hB).
Local Notation MC d := (@CurrentMass.value R h2 (m+n) d AB hAB).
Local Notation P k l := (@CartesianCurrentProduct.value R h2 m n k l A B hA hB).
Local Notation bdA d := (@current_boundary R h2 m d A hA).
Local Notation bdB d := (@current_boundary R h2 n d B hB).
Local Notation bdC d := (@current_boundary R h2 (m+n) d AB hAB).
Local Notation Tr a b e := (@current_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation suppA d := (@current_support R h2 m A hA d).
Local Notation suppB d := (@current_support R h2 n B hB d).
Local Notation suppC d := (@current_support R h2 (m+n) AB hAB d).

(** Source for [current_cartesian_flat_decomposition_zero]:
    for T=A0+boundary B0 and degree(S)=0, the
    original product filling has cost at most
    M(S)(M(A0)+M(B0)), the zero-degree case
    of the first product estimate in Federer
    4.1.12, p. 369. *)
Theorem current_cartesian_flat_decomposition_zero (S:CA 0%N) (A0:CB j) (B0:CB j.+1) a r s:
  MA 0%N S=a%:E->MB j A0=r%:E->MB j.+1 B0=s%:E->
  suppA 0%N S `<=` smooth_compact_carrier KA->
  suppB j A0 `<=` smooth_compact_carrier KB->
  suppB j.+1 B0 `<=` smooth_compact_carrier KB->
  (@current_flat_norm R h2 (m+n) (0+j) AB hAB KAB
    (P 0%N j S (A0+bdB j B0))<=(a*r+a*s)%:E)%E.
Proof.
move=>hMS hMA0 hMB0 hSS hSA0 hSB0.
pose P0:=P 0%N j S A0.
pose H:=Tr _ _ (addnS 0%N j) (P 0%N j.+1 S B0).
pose Target:=P 0%N j S (A0+bdB j B0).
have hP0Support:suppC (0+j) P0 `<=` smooth_compact_carrier KAB:=
  @current_cartesian_compact_support_bound R h2 m n 0%N j A B hA hB KA KB KAB hKAB S A0 hSS hSA0.
have hHSupport:suppC (0+j).+1 H `<=` smooth_compact_carrier KAB.
  rewrite /H current_degree_transport_support.
  exact:(@current_cartesian_compact_support_bound R h2 m n 0%N j.+1 A B hA hB KA KB KAB hKAB
    S B0 hSS hSB0).
have hP0Mass:(MC (0+j) P0<=(a*r)%:E)%E:=
  @current_cartesian_finite_mass_bound R h2 m n 0%N j A B hA hB S A0 a r hMS hMA0.
have hHMass:(MC (0+j).+1 H<=(a*s)%:E)%E.
  rewrite /H current_mass_degree_transport.
  exact:(@current_cartesian_finite_mass_bound R h2 m n 0%N j.+1 A B hA hB S B0 a s hMS hMB0).
have hIdentity:Target = P0+bdC (0+j) H.
  have hLinear:=(@current_cartesian_product_bilinear R h2 m n 0%N j A B hA hB).2 S.
  rewrite /Target (linD hLinear)
    (@current_cartesian_filling_boundary_zero R h2 m n A B hA hB j S B0).
  by [].
have hBdH:suppC (0+j) (bdC (0+j) H) `<=` smooth_compact_carrier KAB.
  move=>x hx;exact:hHSupport x (@current_boundary_support_subset R h2 (m+n) (0+j) AB hAB H x hx).
have hTargetSupport:suppC (0+j) Target `<=` smooth_compact_carrier KAB.
  rewrite hIdentity.
  have h:=@current_support_linear_subset R h2 (m+n) (0+j) AB hAB KAB 1 P0 (bdC (0+j) H)
    hP0Support hBdH.
  by rewrite scale1r in h.
have hFlat:=@current_flat_decomposition_lower_bound R h2 (m+n) (0+j) AB hAB KAB Target H hTargetSupport hHSupport.
have hResidual:Target-bdC (0+j) H = P0 by rewrite hIdentity addrK.
rewrite hResidual in hFlat.
have hCost:=leeD hP0Mass hHMass.
rewrite -EFinD in hCost.
exact:le_trans hFlat hCost.
Qed.
End CurrentCartesianFlatDecompositionZero.
