(** Federer 1.4.5, p. 20, opening assertion: sharp corrected exceptions
    for the ordinary tensor product of scalar alternating forms on V
    and exterior vectors on W. The two spaces may be infinite dimensional.
    Reuse 1.2.1-2 and 1.3.2, with the existing commutator witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import DualExterior OrdinaryTensorObstruction
  IndependentDual PairingSeparation OrdinaryTensorLeftObstruction
  OrdinaryTensorSmallSpaces OrdinaryTensorLowDegrees SmallVectorSpaceAlternatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Classification.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra W).
Local Notation T := (algebra_tensor U E).
Local Notation G := (tensor_grading_product (A_star_grading V K^o)
  (exterior_grading W)).

(** Source for [ordinary_tensor_right_pair_not_commutative]: supporting
    exact classification for Federer 1.4.5, p. 20. An independent pair
    in W suffices for noncommutativity, with no condition on V. Apply
    the existing two-vector commutator using its independent dual forms. *)
Lemma ordinary_tensor_right_pair_not_commutative (d : 'I_2 -> W) :
    finite_independent d -> ~ commutative (alg_mul T).
Proof.
move=> hd.
apply: (@ordinary_tensor_not_commutative K h2 V W
  (independent_dual hd ord0) (independent_dual hd ord_max)
  (d ord0) (d ord_max)); by rewrite independent_dualE.
Qed.

(** Source for [ordinary_tensor_nonzero_factors_not_anticommutative]:
    supporting exact classification for Federer 1.4.5, p. 20. A nonzero
    vector in each factor supplies commuting odd tensors whose product
    has nonzero scalar evaluation. Graded anticommutativity would negate
    this product. Use the existing cross-factor witness and normalized
    functionals of 1.1.1; no independent pair is required. *)
Lemma ordinary_tensor_nonzero_factors_not_anticommutative :
    ~ vector_space_is_zero V -> ~ vector_space_is_zero W ->
    ~ graded_anticommutative G (alg_mul T).
Proof.
move=> hV hW.
have [v hv] := vector_space_not_zero_has_nonzero hV.
have [w hw] := vector_space_not_zero_has_nonzero hW.
have [a ha] := nonzero_functional hv.
have [b hb] := nonzero_functional hw.
exact: (@ordinary_tensor_not_anticommutative K h2 V W b w hb a v ha).
Qed.

(** Source for [ordinary_tensor_small_spaces_commutative]: supporting
    boundary assembly for Federer 1.4.5, p. 20. If each original space
    is zero or has a singleton basis, both factor products and their
    ordinary tensor product are commutative. Include all four boundary
    combinations through the original finite exterior dimension law. *)
Lemma ordinary_tensor_small_spaces_commutative :
    (vector_space_is_zero V \/ vector_space_is_line V) ->
    (vector_space_is_zero W \/ vector_space_is_line W) ->
    commutative (alg_mul T).
Proof.
move=> [hV|[e he]] [hW|[d hd]].
- exact: (@ordinary_tensor_small_factors_commutative K h2 V W 0 0
    (fun _ => 0) (fun _ => 0) (zero_space_empty_basis hV)
    (zero_space_empty_basis hW) (leq0n 1) (leq0n 1)).
- exact: (@ordinary_tensor_small_factors_commutative K h2 V W 0 1
    (fun _ => 0) d (zero_space_empty_basis hV) hd (leq0n 1) (leqnn 1)).
- exact: (@ordinary_tensor_small_factors_commutative K h2 V W 1 0
    e (fun _ => 0) he (zero_space_empty_basis hW) (leqnn 1) (leq0n 1)).
- exact: (@ordinary_tensor_small_factors_commutative K h2 V W 1 1
    e d he hd (leqnn 1) (leqnn 1)).
Qed.

(** Source for [ordinary_tensor_commutative_iff]: sharp corrected
    commutativity classification for the opening of Federer 1.4.5,
    p. 20. The original ordinary product is commutative precisely when
    each of V and W has dimension at most one. This includes zero
    spaces and places no finite-dimensional premise on either space. *)
Theorem ordinary_tensor_commutative_iff :
    commutative (alg_mul T) <->
    (vector_space_is_zero V \/ vector_space_is_line V) /\
    (vector_space_is_zero W \/ vector_space_is_line W).
Proof.
split.
- move=> hc; split; apply: vector_space_without_pair_small => [[e he]].
  + exact: (@ordinary_tensor_left_pair_not_commutative K h2 V W e he hc).
  + exact: (ordinary_tensor_right_pair_not_commutative he hc).
- by move=> [hV hW]; apply: ordinary_tensor_small_spaces_commutative.
Qed.

(** Source for [ordinary_tensor_anticommutative_iff]: sharp corrected
    graded anticommutativity classification for Federer 1.4.5, p. 20.
    The ordinary product is graded anticommutative precisely when one
    original space is zero. The positive direction follows from the
    signed-product law of 1.2.2, because the zero factor has only degree
    zero. This corrects the printed exceptional-case wording. *)
Theorem ordinary_tensor_anticommutative_iff :
    graded_anticommutative G (alg_mul T) <->
    vector_space_is_zero V \/ vector_space_is_zero W.
Proof.
split.
- move=> ha.
  have [hV|hV] := pselect (vector_space_is_zero V); first by left.
  have [hW|hW] := pselect (vector_space_is_zero W); first by right.
  exact: False_ind _ (ordinary_tensor_nonzero_factors_not_anticommutative hV hW ha).
- move=> [hV|hW].
  + exact: ordinary_tensor_zero_left_anticommutative.
  + exact: ordinary_tensor_zero_right_anticommutative.
Qed.

(** Source for [ordinary_tensor_neither_iff]: sharp corrected form of
    Federer 1.4.5, p. 20, opening sentence. The ordinary product is
    neither commutative nor graded anticommutative precisely when both
    original spaces are nonzero and at least one contains an independent
    pair. Equivalently, the exceptions are a zero factor or two lines.
    The already checked zero-space counterexamples remain valid. *)
Theorem ordinary_tensor_neither_iff :
    (~ commutative (alg_mul T) /\
      ~ graded_anticommutative G (alg_mul T)) <->
    (~ vector_space_is_zero V /\ ~ vector_space_is_zero W /\
      (vector_space_has_pair V \/ vector_space_has_pair W)).
Proof.
split.
- move=> [hc ha].
  have hV : ~ vector_space_is_zero V.
    move=> hz; apply: ha; apply/ordinary_tensor_anticommutative_iff; by left.
  have hW : ~ vector_space_is_zero W.
    move=> hz; apply: ha; apply/ordinary_tensor_anticommutative_iff; by right.
  split=> //; split=> //.
  have [hp|hp] := pselect (vector_space_has_pair V); first by left.
  have [hq|hq] := pselect (vector_space_has_pair W); first by right.
  exfalso; apply: hc; apply: ordinary_tensor_small_spaces_commutative;
    exact: vector_space_without_pair_small.
- move=> [hV [hW hp]]; split.
  + case: hp => [[e he]|[d hd]].
    * exact: (@ordinary_tensor_left_pair_not_commutative K h2 V W e he).
    * exact: (ordinary_tensor_right_pair_not_commutative hd).
  + exact: (ordinary_tensor_nonzero_factors_not_anticommutative hV hW).
Qed.
End Classification.
