(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(8), pp. 326,
    329–330: the original prefix subrings
    form an increasing family. Iterate the
    already proved adjacent germ factorisation;
    no new holomorphic argument is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates HolomorphicCoordinateNorm Hom RealNormUP LinearBasis HolomorphicGermRing HolomorphicPrefixGermSubring
  HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilySealed HolomorphicPrefixPolynomialSubring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section NestedPrefixes.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:is_complex_norm NX.
Local Notation hNXR:=(complex_norm_real hNX).
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Local Notation Q:=(@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega).

(** Source for [holomorphic_coordinate_prefix_subring_monotone]:
    Q_p is contained in Q_q for
    p<=q<=n, the nested original coordinate
    rings used in 3.4.8(8), p. 329.
    Every induction step applies the existing
    adjacent prefix factorisation directly. *)
Theorem holomorphic_coordinate_prefix_subring_monotone p q:
  (p<=q)%N ->(q<=n)%N ->Q p `<=` Q q.
Proof.
move=>hPQ hQN.
have hQ:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
have hStep r (hRN:(r<n)%N):Q r `<=` Q r.+1.
  pose j:'I_n:=Ordinal hRN.
  rewrite (holomorphic_coordinate_subring_family_member hQ (leq_trans (leqnSn (j:nat)) (ltn_ord j)))
    (holomorphic_coordinate_subring_family_member hQ (ltn_ord j)).
  move=>alpha /holomorphic_prefix_germ_subring_membership[beta hBeta].
  have [F hF]:=@holomorphic_adjacent_prefix_factorisation R X NX hNX n e he omega j.
  apply/holomorphic_prefix_germ_subring_membership;exists (F beta).
  by rewrite -hF hBeta.
have hLoop r:(p+r<=n)%N ->Q p `<=` Q (p+r)%N.
  elim:r=>[|r IH].
  - rewrite addn0=>_;exact:subset_refl.
  - rewrite addnS=>hBound.
    exact:(subset_trans (IH (leq_trans (leqnSn (p+r)) hBound)) (hStep (p+r)%N hBound)).
have hEnd:(p+(q-p)=q)%N:=subnKC hPQ.
have hFinal:=hLoop (q-p)%N;rewrite hEnd in hFinal.
exact:hFinal hQN.
Qed.
End NestedPrefixes.
