(** Federer (1969), 3.1.15, p. 227:
    "we can apply 3.1.4 to the functions D^alpha f". Theorem 3.1.4
    requires a Lebesgue measurable function, so the continuous map
    D^alpha f on its open domain B is extended by zero to the whole
    space, as f_A in 2.4.10, p. 85. The extension is measurable in
    the sense of 2.3.2, p. 73: the inverse image of an open set is
    the union of an open set and of a closed set or the empty set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness FiniteNormEquivalence RealNormUP
  NormDifferentialUP NormBoundedLinearTopology NormClassOneUP NormClassZeroTopology
  EuclideanPartitionOverlapNeighborhood EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  TopologicalBorel MeasureUP MeasureSplit MeasureFiniteClosure MeasureAlmostUP
  MeasureAlmostBasic MeasurableFunctionUP PartialFunctionUP PartialFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section ZeroExtension.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation Yn := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Variable B : set X.
Variable g : X->Yn.
Hypothesis hg : norm_class_zero N NY B g.

(** Source for [inner_norm_domain_open]: a set containing a norm
    ball about each of its points is open, Federer 2.2.1, p. 60,
    in the topology of the inner product of 1.7.1, p. 28; converse
    of the library adapter used for 3.1.13, pp. 224–225. *)
Lemma inner_norm_domain_open (U : set X) :
  (forall a, U a -> norm_domain_interior N U a) -> open U.
Proof.
move=>hU; rewrite openE=>a ha.
apply: (inner_real_norm_same_nbhs (@euclidean_inner_productP R m) a U).2.
exact: ((norm_domain_interior_neighbourhood hN U a).1 (hU a ha)).
Qed.

(** Source for [zero_extension_domain_open]: the domain of a map of
    class zero is open, Federer 3.1.1, p. 210, in the topology of
    the Euclidean inner product, 3.1.15, p. 227. *)
Lemma zero_extension_domain_open : open B.
Proof. apply: inner_norm_domain_open=>a ha; exact: (hg ha).1. Qed.

(** Source for [zero_extension]: the function equal to g on B and
    to zero elsewhere, as in Federer 2.4.10, p. 85 (f_A), used to
    apply 3.1.4 to D^alpha f in 3.1.15, p. 227. *)
Definition zero_extension (x : X) : Yn := if pselect (B x) then g x else 0.

(** Source for [zero_extension_preimage_open]: on the open domain B
    of a continuous map the inverse image of an open set is open,
    Federer 2.2.1/2.3.2, pp. 60, 73. *)
Lemma zero_extension_preimage_open (U : set Yn) :
  open U -> open [set x | B x /\ U (g x)].
Proof.
move=>hU; apply: inner_norm_domain_open=>a [ha hUa].
have [e [he hUe]] := inner_open_norm_domain hU hUa.
have [r [hr hr']] := norm_class_zero_local_control hN hg ha he.
exists r; split; first exact hr.
move=>h hh.
have [hBh hgh] : B (a+h) /\ NY (g (a+h)-g a)<e.
  apply: hr'; by rewrite (addrC a h) addrK.
split; first exact hBh.
have := hUe _ hgh; by rewrite (addrC (g a)) subrK.
Qed.

(** Source for [zero_extension_preimage]: the inverse image of an
    open set under the zero extension, Federer 2.3.2, p. 73, is the
    union of the inverse image under g restricted to B and, when the
    open set contains zero, of the complement of B. *)
Lemma zero_extension_preimage (U : set Yn) :
  partial_function_preimage (partial_function_total zero_extension) U
    = [set x | B x /\ U (g x)] `|` (if pselect (U 0) then ~` B else set0).
Proof.
apply/seteqP; split=>x.
- move=>[y [hy hUy]].
  have hy' : zero_extension x = y by exact hy.
  rewrite -hy' /zero_extension in hUy; move: hUy.
  case: (pselect (B x))=>[hBx hUg|hBx hU0]; first by left.
  right; case: (pselect (U 0))=>[hU0'|hnU0]; first exact hBx.
  exact: (hnU0 hU0).
- move=>[[hBx hUg]|].
  + exists (g x); split; last exact hUg.
    change (zero_extension x = g x); rewrite /zero_extension.
    by case: (pselect (B x)).
  + case: (pselect (U 0))=>[hU0 hnB|hnU0 hx]; last by case: hx.
    exists 0; split; last exact hU0.
    change (zero_extension x = 0); rewrite /zero_extension.
    by case: (pselect (B x)).
Qed.

(** Source for [zero_extension_measurable]: the zero extension is
    Lebesgue measurable, Federer 2.3.2, p. 73: inverse images of
    open sets are the union of an open set and of a closed set or
    the empty set, hence Borel, hence L^m measurable by 2.6.5, p. 120. *)
Theorem zero_extension_measurable :
  @is_measure_measurable_function R [the choiceType of X] [the topologicalType of Yn]
    (@euclidean_lebesgue_measure R m) (partial_function_total zero_extension).
Proof.
have hm := euclidean_lebesgue_is_measure R m.
split.
- rewrite partial_function_total_domain; exact: (measure_almost_everywhere_true hm).
move=>U hU; rewrite zero_extension_preimage.
apply: (measure_measurable_union hm).
- apply: euclidean_borel_measurable; apply: open_borel_set.
  exact: (zero_extension_preimage_open hU).
case: (pselect (U 0))=>[hU0|hnU0]; last exact: (measure_measurable_empty hm).
exact: (euclidean_borel_measurable (closed_borel_set (open_closedC zero_extension_domain_open))).
Qed.
End ZeroExtension.
