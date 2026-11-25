(** Federer (1969), 4.1.12, p. 369: the
    original mass decomposition gives the first flat
    product estimate. In positive first degree, the
    first-factor boundary contributes its own product
    mass. Every sign and support is retained. *)
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
Section CurrentCartesianFlatDecompositionPositive.
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

(** Source for [current_cartesian_flat_decomposition_positive]:
    for T=A0+boundary B0, the original product
    admits a filling of cost at most
    M(S)M(A0)+M(boundary S)M(B0)+M(S)M(B0).
    This is the mass-minimum proof of the first
    product inequality in Federer 4.1.12, p. 369,
    using 4.1.8's positive-degree boundary formula. *)
Theorem current_cartesian_flat_decomposition_positive (S:CA i.+1) (A0:CB j) (B0:CB j.+1) a b r s:
  MA i.+1 S=a%:E->MA i (bdA i S)=b%:E->MB j A0=r%:E->MB j.+1 B0=s%:E->
  suppA i.+1 S `<=` smooth_compact_carrier KA->
  suppB j A0 `<=` smooth_compact_carrier KB->
  suppB j.+1 B0 `<=` smooth_compact_carrier KB->
  (@current_flat_norm R h2 (m+n) (i.+1+j) AB hAB KAB
    (P i.+1 j S (A0+bdB j B0))<=(a*r+b*s+a*s)%:E)%E.
Proof.
move=>hMS hMBdS hMA0 hMB0 hSS hSA0 hSB0.
pose c:=(-1:R)^+i.+1.
pose P0:=P i.+1 j S A0.
pose Q:=Tr _ _ (eq_trans (addnS i j) (esym (addSn i j))) (P i j.+1 (bdA i S) B0).
pose H0:=Tr _ _ (addnS i.+1 j) (P i.+1 j.+1 S B0).
pose Resid:=(-c)*:Q+P0.
pose H:=c*:H0.
pose Target:=P i.+1 j S (A0+bdB j B0).
have hBdS:suppA i (bdA i S) `<=` smooth_compact_carrier KA.
  move=>x hx;exact:hSS x (@current_boundary_support_subset R h2 m i A hA S x hx).
have hP0Support:suppC (i.+1+j) P0 `<=` smooth_compact_carrier KAB:=
  @current_cartesian_compact_support_bound R h2 m n i.+1 j A B hA hB KA KB KAB hKAB S A0 hSS hSA0.
have hQSupport:suppC (i.+1+j) Q `<=` smooth_compact_carrier KAB.
  rewrite /Q current_degree_transport_support.
  exact:(@current_cartesian_compact_support_bound R h2 m n i j.+1 A B hA hB KA KB KAB hKAB
    (bdA i S) B0 hBdS hSB0).
have hH0Support:suppC (i.+1+j).+1 H0 `<=` smooth_compact_carrier KAB.
  rewrite /H0 current_degree_transport_support.
  exact:(@current_cartesian_compact_support_bound R h2 m n i.+1 j.+1 A B hA hB KA KB KAB hKAB
    S B0 hSS hSB0).
have hResidSupport:suppC (i.+1+j) Resid `<=` smooth_compact_carrier KAB.
  exact:(@current_support_linear_subset R h2 (m+n) (i.+1+j) AB hAB KAB (-c) Q P0 hQSupport hP0Support).
have hHSupport:suppC (i.+1+j).+1 H `<=` smooth_compact_carrier KAB.
  have h:=@current_support_linear_subset R h2 (m+n) (i.+1+j).+1 AB hAB KAB c H0 0
    hH0Support (@current_support_zero_subset R h2 (m+n) (i.+1+j).+1 AB hAB KAB).
  by rewrite addr0 in h.
have hP0Mass:(MC (i.+1+j) P0<=(a*r)%:E)%E:=
  @current_cartesian_finite_mass_bound R h2 m n i.+1 j A B hA hB S A0 a r hMS hMA0.
have hQMass:(MC (i.+1+j) Q<=(b*s)%:E)%E.
  rewrite /Q current_mass_degree_transport.
  exact:(@current_cartesian_finite_mass_bound R h2 m n i j.+1 A B hA hB (bdA i S) B0 b s hMBdS hMB0).
have hH0Mass:(MC (i.+1+j).+1 H0<=(a*s)%:E)%E.
  rewrite /H0 current_mass_degree_transport.
  exact:(@current_cartesian_finite_mass_bound R h2 m n i.+1 j.+1 A B hA hB S B0 a s hMS hMB0).
have hResidMass:(MC (i.+1+j) Resid<=(b*s+a*r)%:E)%E.
  have h:=@current_finite_mass_linear_bound R h2 (m+n) (i.+1+j) AB hAB (-c) Q P0 (b*s) (a*r)
    hQMass hP0Mass.
  by rewrite normrN /c normrX normrN normr1 expr1n mul1r in h.
have hHMass:(MC (i.+1+j).+1 H<=(a*s)%:E)%E.
  have h:=@current_finite_mass_scale_bound R h2 (m+n) (i.+1+j).+1 AB hAB c H0 (a*s) hH0Mass.
  by rewrite /c normrX normrN normr1 expr1n mul1r in h.
have hIdentity:Target=Resid+bdC (i.+1+j) H.
  have hLinear:=(@current_cartesian_product_bilinear R h2 m n i.+1 j A B hA hB).2 S.
  rewrite /Target (linD hLinear)
    (@current_cartesian_filling_boundary_positive R h2 m n A B hA hB i j S B0).
  change (P0+((-c)*:Q+bdC (i.+1+j) H)=((-c)*:Q+P0)+bdC (i.+1+j) H).
  by rewrite addrA [P0+(-c)*:Q]addrC.
have hBdH:suppC (i.+1+j) (bdC (i.+1+j) H) `<=` smooth_compact_carrier KAB.
  move=>x hx;exact:hHSupport x (@current_boundary_support_subset R h2 (m+n) (i.+1+j) AB hAB H x hx).
have hTargetSupport:suppC (i.+1+j) Target `<=` smooth_compact_carrier KAB.
  rewrite hIdentity.
  have h:=@current_support_linear_subset R h2 (m+n) (i.+1+j) AB hAB KAB 1 Resid (bdC (i.+1+j) H)
    hResidSupport hBdH.
  by rewrite scale1r in h.
have hFlat:=@current_flat_decomposition_lower_bound R h2 (m+n) (i.+1+j) AB hAB KAB Target H hTargetSupport hHSupport.
have hResidual:Target-bdC (i.+1+j) H=Resid by rewrite hIdentity addrK.
rewrite hResidual in hFlat.
have hCost:=leeD hResidMass hHMass.
rewrite -EFinD in hCost.
have h:=le_trans hFlat hCost.
by rewrite [b*s+a*r]addrC in h.
Qed.
End CurrentCartesianFlatDecompositionPositive.
