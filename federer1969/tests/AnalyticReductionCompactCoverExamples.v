(** Actual boundary and nonreduced regressions for the stronger
    auxiliary compact-union assertion in Federer (1969), 3.4.8(5),
    p. 328. All original ideal and geometric premises are proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct OrthonormalFamilies EuclideanStiefelInnerSplitting InnerNorm InnerMetric HomInner LinearGroupTopology HilbertFormCompactness AnalyticGermUP AnalyticGermRing
  AnalyticGermDomain CommutativeIdealUP CommutativeFactorizationUP CommutativeDivisibility
  CommutativeDomainCancellation AnalyticReductionActual AnalyticReductionECompactCover
  IncreasingCompactCoverUP OrthogonalGroupTopology.
From FedererTests Require Import LocalAlgebraExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_ambient_reduction_compact_cover_regression]:
    actual R^0 and the zero proper ideal retain every original
    E index in Federer 3.4.8(5), p. 328; this is an added regression. *)
Example zero_ambient_reduction_compact_cover_regression (R:realType):
  let X:=R_n R 0 in
  let hB:=@euclidean_inner_productP R 0 in
  let G:=[the comNzRingType of (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0)] in
  forall m:'I_1,exists K:nat->set (@orthogonal_group R X (@euclidean_inner_product R 0)
    hB 0 (@coordinate_basis R 0) (@coordinate_basisP R 0)),
    is_increasing_compact_cover (@analytic_reduction_actual_E R X (@euclidean_inner_product R 0)
      hB 0 (@coordinate_basis R 0) (@coordinate_basisP R 0) (dual_basis (@coordinate_basisP R 0))
      [set z:G|z = 0] m) K.
Proof.
move=>X hB G m.
have hI:is_commutative_ideal [set z:G|z = 0].
  constructor.
  - reflexivity.
  - by move=>x y -> ->;rewrite addr0.
  - by move=>x ->;rewrite oppr0.
  - by move=>x y ->;rewrite mulr0.
have hProper:~([set z:G|z = 0] 1).
  move=>h;have hh:=oner_neq0 G;by rewrite h eqxx in hh.
apply:(@analytic_reduction_actual_E_compact_cover R X (@euclidean_inner_product R 0) hB
  0 (@coordinate_basis R 0) (@coordinate_basisP R 0) (@euclidean_coordinate_orthonormal_family R 0)
  (dual_basis (@coordinate_basisP R 0)) _ _ m hI hProper).
by move=>i j;rewrite dual_basisE eq_sym.
Qed.

(** Source for [nonreduced_square_ideal_compact_cover_regression]:
    the original one-variable ideal (x^2) is proper and contains x^2
    but not x. The full auxiliary assertion of Federer 3.4.8(5),
    p. 328 applies to every E index of this actual nonreduced ideal;
    this is an added regression, not an extra theorem hypothesis. *)
Example nonreduced_square_ideal_compact_cover_regression (R:realType):
  let X:=R_n R 1 in
  let hB:=@euclidean_inner_productP R 1 in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)] in
  exists I:set G,exists alpha:G,
    is_commutative_ideal I /\~I 1 /\I (alpha*alpha) /\~I alpha /\
    forall m:'I_2,exists K:nat->set (@orthogonal_group R X (@euclidean_inner_product R 1)
      hB 1 (@coordinate_basis R 1) (@coordinate_basisP R 1)),
      is_increasing_compact_cover (@analytic_reduction_actual_E R X (@euclidean_inner_product R 1)
        hB 1 (@coordinate_basis R 1) (@coordinate_basisP R 1) (dual_basis (@coordinate_basisP R 1)) I m) K.
Proof.
move=>X hB NX hNX G.
have [f [hValues [hNonzero [hNonunit hRest]]]]:=@local_algebra_square_regression R.
pose alpha:G:=analytic_germ f.
pose I:set G:=commutative_divides (alpha*alpha).
have hI:is_commutative_ideal I.
  constructor.
  - exact:commutative_divides_zero.
  - move=>x y;exact:commutative_divides_add.
  - move=>x;exact:commutative_divides_negate.
  - move=>x y;exact:commutative_divides_multiply.
have hProper:~I 1.
  move=>[z hOne];apply:hNonunit;exists (z*alpha).
  by rewrite -mulrA -hOne.
have hNotMember:~I alpha.
  move=>[z hEqual];apply:hNonunit;exists z.
  apply:(@commutative_domain_cancel_left G (@analytic_germ_no_zero_divisors R X NX hNX 0)
    alpha (z*alpha) 1 hNonzero).
  by rewrite mulr1 mulrCA -hEqual.
exists I,alpha;split;first exact:hI.
split;first exact:hProper.
split;first exact:commutative_divides_reflexive.
split;first exact:hNotMember.
move=>m.
apply:(@analytic_reduction_actual_E_compact_cover R X (@euclidean_inner_product R 1) hB
  1 (@coordinate_basis R 1) (@coordinate_basisP R 1) (@euclidean_coordinate_orthonormal_family R 1)
  (dual_basis (@coordinate_basisP R 1)) _ I m hI hProper).
by move=>i j;rewrite dual_basisE eq_sym.
Qed.
