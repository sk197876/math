(** Federer (1969), 2.10.38, printed pp. 198–199: repeatedly choose a
    maximal chord and project to its perpendicular hyperplane. This
    supporting specification records the axes, selected chords, their
    lengths and the abstract residual maps. The recursion and maximality
    laws precede the existence proof. Sorted lengths and exterior-product
    formulas are consequences, not assumed fields. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerMetric
  InnerNorm OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [greedy_chord_frame_data]: supporting
    finite axes and chords with residual maps
    for the induction in 2.10.38,
    pp. 198–199. Laws are specified separately. *)
Record greedy_chord_frame_data (R : realType) (n : nat) := {
  (** Source for [greedy_chord_axis]: supporting ordered
      perpendicular chord directions in 2.10.38,
      p. 199. *)
  greedy_chord_axis : 'I_n -> R_n R n;
  (** Source for [greedy_chord_length]: supporting widths
      c_i in 2.10.38, pp. 198–199. *)
  greedy_chord_length : 'I_n -> R;
  (** Source for [greedy_chord_first]: supporting selected
      source endpoints a_i in 2.10.38,
      pp. 198–199. *)
  greedy_chord_first : 'I_n -> R_n R n;
  (** Source for [greedy_chord_second]: supporting selected
      source endpoints b_i in 2.10.38,
      pp. 198–199. *)
  greedy_chord_second : 'I_n -> R_n R n;
  (** Source for [greedy_chord_residual]: supporting successive
      perpendicular projections in 2.10.38,
      p. 199. Their recursive equations are laws,
      not an exposed recursive implementation. *)
  greedy_chord_residual : nat -> {linear R_n R n -> R_n R n}
}.

(** Source for [is_greedy_chord_frame]: supporting
    intrinsic maximal-chord specification for the
    proof of 2.10.38, p. 199.
    Orthogonality, residual recursion and maximality
    suffice to derive the sorted box widths
    and all initial exterior-product equalities. *)
Record is_greedy_chord_frame (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (D : greedy_chord_frame_data R n) : Prop := {
  (** Source for [greedy_chord_orthonormal_law]: supporting
      perpendicular unit axes chosen in 2.10.38,
      p. 199. *)
  greedy_chord_orthonormal_law : orthonormal_family (@euclidean_inner_product R n)
    (greedy_chord_axis D);
  (** Source for [greedy_chord_endpoints_law]: direct
      requirement a_i,b_i in S in 2.10.38,
      p. 198. *)
  greedy_chord_endpoints_law : forall i,
    S (greedy_chord_first D i) /\ S (greedy_chord_second D i);
  (** Source for [greedy_chord_residual_zero_law]: supporting
      original-space starting projection in 2.10.38,
      p. 199. *)
  greedy_chord_residual_zero_law : forall v, greedy_chord_residual D 0 v=v;
  (** Source for [greedy_chord_residual_successor_law]: supporting
      removal of each chosen normal component in
      2.10.38, p. 199. This is the
      intrinsic form of the successive perpendicular
      coordinate projections in the printed induction. *)
  greedy_chord_residual_successor_law : forall i : 'I_n, forall v,
    greedy_chord_residual D i.+1 v=greedy_chord_residual D i v-
      euclidean_inner_product v (greedy_chord_axis D i)*:greedy_chord_axis D i;
  (** Source for [greedy_chord_selected_law]: supporting
      chosen maximal chord along each new axis
      in 2.10.38, p. 199. *)
  greedy_chord_selected_law : forall i : 'I_n,
    greedy_chord_residual D i (greedy_chord_first D i-greedy_chord_second D i)=
      greedy_chord_length D i*:greedy_chord_axis D i;
  (** Source for [greedy_chord_maximal_law]: supporting
      attained diameter in each successive projected
      source in 2.10.38, p. 199. *)
  greedy_chord_maximal_law : forall i : 'I_n, forall x y, S x -> S y ->
    inner_norm (@euclidean_inner_productP R n) (greedy_chord_residual D i (x-y))<=
      greedy_chord_length D i
}.
