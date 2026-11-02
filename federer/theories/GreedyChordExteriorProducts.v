(** Federer (1969), 2.10.38, printed pp. 198–199: the norm of each initial
    product of selected endpoint differences equals the product of the
    corresponding widths. Derive this from the public maximal-chord laws and
    exterior algebra. The statements below include an empty initial product
    and zero widths. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerMetric GreedyChordFrameUP GreedyChordFrameLaws GreedyChordFrameExpansion
  FinitePrefixes FiniteSpans FiniteSpanTransfer SimpleOrthonormalBasis
  OrthonormalFamilies FiniteExteriorPowers ExteriorGrading ExteriorNorm
  ExteriorDiameterUP TriangularExteriorScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Products.
Variable R : realType.
Variable n : nat.
Variable S : set (inner_metric_space (@euclidean_inner_productP R n)).
Variable D : greedy_chord_frame_data R n.
Hypothesis hD : is_greedy_chord_frame S D.
Local Notation e := (greedy_chord_axis D).
Local Notation a := (greedy_chord_first D).
Local Notation b := (greedy_chord_second D).
Local Notation c := (greedy_chord_length D).

(** Source for [greedy_chord_prefix_product]: supporting
    triangular exterior identity for the equality in
    2.10.38, p. 199. For any initial length,
    the endpoint product is the product of widths
    times the exterior product of the chosen axes. *)
Lemma greedy_chord_prefix_product k (hk : (k<=n)%N) :
  exterior_difference_product (family_prefix hk a) (family_prefix hk b)=
    (\prod_(i<k) family_prefix hk c i)*:
      e_lambda (family_prefix hk e) (ord_tuple k).
Proof.
apply: triangular_exterior_product_scaling=> i.
pose j := widen_ord hk i.
apply: (proj2 (@finite_span_extensional R (R_n R n) i
  (family_prefix (ltnW (ltn_ord i)) (family_prefix hk e))
  (family_prefix (ltnW (ltn_ord j)) e) _ _)) (greedy_chord_triangular hD j).
move=> l; exact: family_prefix_compose.
Qed.

(** Source for [greedy_chord_prefix_norm]: direct norm
    equality of 2.10.38, pp. 198–199,
    for all initial lengths, strengthened to include
    length zero. Zero widths require no cancellation. *)
Theorem greedy_chord_prefix_norm k (hk : (k<=n)%N) :
  exterior_difference_norm (family_prefix hk a) (family_prefix hk b)=
    \prod_(i<k) family_prefix hk c i.
Proof.
rewrite /exterior_difference_norm greedy_chord_prefix_product exterior_norm_scale.
rewrite (orthonormal_product_unit_norm (real_exterior_two_nonzero R)
  (@euclidean_inner_productP R n)
  (@orthonormal_family_prefix R (R_n R n) _ n e
    (greedy_chord_orthonormal_law hD) k hk)) mulr1.
apply: ger0_norm; apply: prodr_ge0=> i _.
exact (@greedy_chord_length_nonnegative R n S D hD (widen_ord hk i)).
Qed.
End Products.
