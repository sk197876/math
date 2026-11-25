(** Federer (1969), 2.10.29, p. 194: existence of the interleaved
    subdivision sequences. The private state contains the two positive
    current widths. Choose the first split small relative to the second
    width, then the second split small relative to the newly chosen first
    width. Only the final recurrence laws will be exposed by opaque module
    ascription. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ConcaveIntervalGaugeUP CantorSplitRadiusUP CantorSplitRadius
  CantorSplitSmallSpacing InterleavedCantorScalesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_cantor_width_state]: private
    existence-state data for the two positive
    current widths in 2.10.29, p. 194.
    It is not an additional public hypothesis. *)
Record positive_cantor_width_state (R : realType) := {
  (** Source for [positive_width_left]: private
      first current width supporting 2.10.29, p. 194. *)
  positive_width_left : R;
  (** Source for [positive_width_right]: private
      second current width supporting 2.10.29, p. 194. *)
  positive_width_right : R;
  (** Source for [positive_width_left_law]: private
      positive-length invariant supporting the
      next first split in 2.10.29, p. 194. *)
  positive_width_left_law : 0<positive_width_left;
  (** Source for [positive_width_right_law]: private
      positive-length invariant supporting the
      next second split in 2.10.29, p. 194. *)
  positive_width_right_law : 0<positive_width_right
}.

(** Source for [interleaved_cantor_step_data]: private
    six scalar choices made at one stage of
    2.10.29, p. 194, before verifying their laws. *)
Record interleaved_cantor_step_data (R : realType) := {
  (** Source for [step_left_number]: private n_j
      choice supporting 2.10.29, p. 194. *)
  step_left_number : nat;
  (** Source for [step_left_width]: private s_j
      choice supporting 2.10.29, p. 194. *)
  step_left_width : R;
  (** Source for [step_left_spacing]: private t_j
      choice supporting 2.10.29, p. 194. *)
  step_left_spacing : R;
  (** Source for [step_right_number]: private nu_j
      choice supporting 2.10.29, p. 194. *)
  step_right_number : nat;
  (** Source for [step_right_width]: private sigma_j
      choice supporting 2.10.29, p. 194. *)
  step_right_width : R;
  (** Source for [step_right_spacing]: private tau_j
      choice supporting 2.10.29, p. 194. *)
  step_right_spacing : R
}.

(** Source for [is_interleaved_cantor_step]: private
    one-step recurrence predicate for 2.10.29,
    p. 194. Existence is proved below by
    two successive arbitrarily small spacing choices. *)
Record is_interleaved_cantor_step (R : realType) (h : R -> R) (j : nat) (a b : R)
    (D : interleaved_cantor_step_data R) : Prop := {
  (** Source for [step_left_count_law]: private n_j>=2
      law supporting 2.10.29, p. 194. *)
  step_left_count_law : (2<=step_left_number D)%N;
  (** Source for [step_left_split_law]: private first
      equal-cost law supporting 2.10.29, p. 194. *)
  step_left_split_law : is_cantor_split_radius h a (step_left_number D) (step_left_width D);
  (** Source for [step_left_spacing_law]: private first
      spacing formula supporting 2.10.29, p. 194. *)
  step_left_spacing_law : step_left_spacing D=cantor_split_spacing a (step_left_number D) (step_left_width D);
  (** Source for [step_left_small_law]: private t_j<=sigma_(j-1)^j
      law supporting 2.10.29, p. 194. *)
  step_left_small_law : step_left_spacing D<=b^+j.+1;
  (** Source for [step_right_count_law]: private nu_j>=2
      law supporting 2.10.29, p. 194. *)
  step_right_count_law : (2<=step_right_number D)%N;
  (** Source for [step_right_split_law]: private second
      equal-cost law supporting 2.10.29, p. 194. *)
  step_right_split_law : is_cantor_split_radius h b (step_right_number D) (step_right_width D);
  (** Source for [step_right_spacing_law]: private second
      spacing formula supporting 2.10.29, p. 194. *)
  step_right_spacing_law : step_right_spacing D=cantor_split_spacing b (step_right_number D) (step_right_width D);
  (** Source for [step_right_small_law]: private tau_j<=s_j^j
      law supporting 2.10.29, p. 194. *)
  step_right_small_law : step_right_spacing D<=(step_left_width D)^+j.+1
}.

(** Source for [interleaved_cantor_step_exists]: supporting
    one induction step in 2.10.29, p. 194.
    First choose t_j against the old second
    width, then tau_j against the new first
    width. Both target errors are positive. *)
Theorem interleaved_cantor_step_exists (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) j (a b : R) :
  0<a -> 0<b -> exists D, is_interleaved_cantor_step h j a b D.
Proof.
move=> ha hb.
have hbe : 0<b^+j.+1 by rewrite exprn_gt0.
have [n [s [t [hn [hs [ht [htpos htSmall]]]]]]] :=
  @cantor_split_spacing_small_exists R h hg a (b^+j.+1) ha hbe.
have hspos := (cantor_split_radius_bounds hs).1.
have hse : 0<s^+j.+1 by rewrite exprn_gt0.
have [nu [sigma [tau [hnu [hr [hTau [hTauPos hTauSmall]]]]]]] :=
  @cantor_split_spacing_small_exists R h hg b (s^+j.+1) hb hse.
exists (@Build_interleaved_cantor_step_data R n s t nu sigma tau); constructor=> /=.
- exact hn.
- exact hs.
- exact ht.
- exact: ltW htSmall.
- exact hnu.
- exact hr.
- exact hTau.
- exact: ltW hTauSmall.
Qed.

(** Source for [interleaved_cantor_selected_step]: private
    choice of a proved one-step witness in
    2.10.29, p. 194. Its data and laws
    stay behind the final opaque scale interface. *)
Definition interleaved_cantor_selected_step (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) j (p : positive_cantor_width_state R) :=
  cid (@interleaved_cantor_step_exists R h hg j (positive_width_left p) (positive_width_right p)
    (positive_width_left_law p) (positive_width_right_law p)).

(** Source for [interleaved_cantor_width_successor]: private
    positive next-width state in the recursion
    of 2.10.29, p. 194. Its positivity
    is supplied by the proved split laws. *)
Definition interleaved_cantor_width_successor (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (j : nat) (p : positive_cantor_width_state R) : positive_cantor_width_state R.
Proof.
pose q := @interleaved_cantor_selected_step R h hg j p.
exact (@Build_positive_cantor_width_state R (step_left_width (projT1 q)) (step_right_width (projT1 q))
  (cantor_split_radius_bounds (step_left_split_law (projT2 q))).1
  (cantor_split_radius_bounds (step_right_split_law (projT2 q))).1).
Defined.

(** Source for [interleaved_cantor_width_states]: private
    recursive existence witness of the widths
    s_j,sigma_j in 2.10.29, p. 194,
    starting at (1,1). *)
Fixpoint interleaved_cantor_width_states (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (j : nat) : positive_cantor_width_state R :=
  if j is k.+1 then @interleaved_cantor_width_successor R h hg k
    (@interleaved_cantor_width_states R h hg k)
  else @Build_positive_cantor_width_state R 1 1 (@ltr01 R) (@ltr01 R).

(** Source for [interleaved_cantor_scale_witness]: private
    six-sequence witness assembled from the
    proved recursive states and selected splits
    for 2.10.29, p. 194. *)
Definition interleaved_cantor_scale_witness (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) : interleaved_cantor_scale_data R :=
  @Build_interleaved_cantor_scale_data R
    (fun j=>step_left_number (projT1 (@interleaved_cantor_selected_step R h hg j
      (@interleaved_cantor_width_states R h hg j))))
    (fun j=>step_right_number (projT1 (@interleaved_cantor_selected_step R h hg j
      (@interleaved_cantor_width_states R h hg j))))
    (fun j=>positive_width_left (@interleaved_cantor_width_states R h hg j))
    (fun j=>positive_width_right (@interleaved_cantor_width_states R h hg j))
    (fun j=>step_left_spacing (projT1 (@interleaved_cantor_selected_step R h hg j
      (@interleaved_cantor_width_states R h hg j))))
    (fun j=>step_right_spacing (projT1 (@interleaved_cantor_selected_step R h hg j
      (@interleaved_cantor_width_states R h hg j)))).

(** Source for [interleaved_cantor_scales_exist]: direct
    existence of the interleaved subdivisions
    and widths in the first paragraph of
    2.10.29, p. 194, generalised to any
    admitted concave gauge. The law predicate
    does not assume the target interleaving,
    convergence or product-measure conclusion. *)
Theorem interleaved_cantor_scales_exist (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) : exists D, is_interleaved_cantor_scales h D.
Proof.
exists (@interleaved_cantor_scale_witness R h hg).
have hstep j := projT2 (@interleaved_cantor_selected_step R h hg j
  (@interleaved_cantor_width_states R h hg j)).
constructor.
- by [].
- by [].
- move=> j; exact (step_left_count_law (hstep j)).
- move=> j; exact (step_right_count_law (hstep j)).
- move=> j; exact (step_left_split_law (hstep j)).
- move=> j; exact (step_right_split_law (hstep j)).
- move=> j; exact (step_left_spacing_law (hstep j)).
- move=> j; exact (step_right_spacing_law (hstep j)).
- move=> j; exact (step_left_small_law (hstep j)).
- move=> j; exact (step_right_small_law (hstep j)).
Qed.
