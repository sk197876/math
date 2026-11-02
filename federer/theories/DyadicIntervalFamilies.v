(** Supporting open-set approximation for Federer (1969), 2.9.20, p. 166. We
    reuse the project's increasing finite dyadic unions from the uniqueness
    proof for 2.5.17, p. 111, instead of constructing all open connected
    components. This is a proof-route departure, not an additional
    hypothesis or a claim that Federer specifies these grids. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground LebesgueLineCharacterisation
  OrderedIntervalFamilyUP OrderedIntervalFamilyConcatenation
  OrderedIntervalFamilyFiltering SegmentRelativeContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dyadic_interval_family]: supporting finite ordered family
    for the open-set step in Federer 2.9.20, p. 166 List the first k
    intervals of the already proved dyadic grid in their natural order. This
    finite enumeration supplies family witnesses only. *)
Definition dyadic_interval_family (R : realType) (n k : nat) : seq (R * R) :=
  [seq (@dyadic_left R n j, @dyadic_left R n j+@dyadic_step R n) | j <- iota 0 k].
Arguments dyadic_interval_family {R} n k.

(** Source for [dyadic_interval_family_succ]: supporting last-cell
    decomposition for Federer 2.9.20, p. 166, finite-union step. *)
Lemma dyadic_interval_family_succ (R : realType) (n k : nat) :
  @dyadic_interval_family R n k.+1=dyadic_interval_family n k++
    [:: (@dyadic_left R n k, @dyadic_left R n k+@dyadic_step R n)].
Proof. by rewrite /dyadic_interval_family -addn1 iotaD add0n /= map_cat. Qed.

(** Source for [dyadic_interval_family_ordered]: supporting eligibility
    of the grid family used for Federer 2.9.20, p. 166. Adjacent
    dyadic cells meet only at their boundary and have positive length. *)
Lemma dyadic_interval_family_ordered (R : realType) (n k : nat) :
  is_ordered_real_interval_family (@dyadic_left R n 0) (@dyadic_left R n k)
    (@dyadic_interval_family R n k).
Proof.
elim: k=> [//|k ih].
have hstep := @dyadic_step_gt0 R n.
have hleft : @dyadic_left R n 0<=@dyadic_left R n k.
  rewrite /dyadic_left mul0r addr0 lerDl.
  exact: mulr_ge0 (ler0n R k) (ltW hstep).
have hnext : @dyadic_left R n k<@dyadic_left R n k.+1.
  by rewrite dyadic_left_succ_index ltrDl.
rewrite dyadic_interval_family_succ.
apply: ordered_real_interval_family_cat hleft (ltW hnext) ih _.
split; first exact: lexx.
split; first by rewrite ltrDl.
split; first by rewrite dyadic_left_succ_index.
by [].
Qed.

(** Source for [selected_dyadic_interval_family]: supporting finite
    subfamily in the open-set step of Federer 2.9.20, p. 166 Keep precisely
    the cells whose half-open intervals lie in S. The selection is expressed
    by its exact membership law below. *)
Definition selected_dyadic_interval_family (R : realType) (S : set R) (n k : nat) :=
  [seq uv <- @dyadic_interval_family R n k | asbool ((`[uv.1,uv.2[ : set R) `<=` S)].

(** Source for [selected_dyadic_interval_family_member]: supporting
    exact membership law for the finite approximation used in
    Federer 2.9.20, p. 166. A selected cell has an index below
    k and is wholly contained in S, with no choice of a cover. *)
Lemma selected_dyadic_interval_family_member (R : realType) (S : set R)
    (n k : nat) (uv : R * R) :
  uv \in selected_dyadic_interval_family S n k <-> exists j : nat,
    (j<k)%N /\ uv=(@dyadic_left R n j, @dyadic_left R n j+@dyadic_step R n) /\
    @dyadic_cell R n j `<=` S.
Proof.
rewrite /selected_dyadic_interval_family mem_filter; split.
- move=> /andP[/asboolP hsub /mapP[j hj heq]].
  have hjk : (j<k)%N by move: hj; rewrite mem_iota add0n leq0n.
  exists j; split=> //; split=> //.
  by rewrite /dyadic_cell; rewrite heq in hsub.
- move=> [j [hjk [heq hsub]]]; apply/andP; split.
  + apply/asboolP; by rewrite heq.
  + apply/mapP; exists j=> //; by rewrite mem_iota add0n leq0n.
Qed.

(** Source for [selected_dyadic_interval_family_ordered]: supporting finite
    family in the reduction of the open-set assertion of Federer 2.9.20, p.
    166 Cells contained in (a,b) form an eligible family in [a,b]; their
    excluded right endpoints may equal b. *)
Lemma selected_dyadic_interval_family_ordered (R : realType) (S : set R)
    (a b : R) (n k : nat) : S `<=` `]a,b[ ->
  is_ordered_real_interval_family a b (selected_dyadic_interval_family S n k).
Proof.
move=> hS.
have hgrid := @dyadic_interval_family_ordered R n k.
have hfilter := ordered_real_interval_family_filter
  (fun uv : R * R => asbool ((`[uv.1,uv.2[ : set R) `<=` S)) hgrid.
apply: ordered_real_interval_family_reset_bounds hfilter _=> u v huv.
have [j [hjk [heq hsub]]] := (selected_dyadic_interval_family_member S n k (u,v)).1 huv.
have hu : u=@dyadic_left R n j := congr1 fst heq.
have hv : v=@dyadic_left R n j+@dyadic_step R n := congr1 snd heq.
have huv' : u<v by rewrite hu hv ltrDl; exact: dyadic_step_gt0.
have hcell : (`[u,v[ : set R) `<=` `]a,b[.
  by rewrite hu hv; exact: subset_trans hsub hS.
have [hau hvb] := half_open_interval_inside_open_bounds huv' hcell.
split=> //; exact: ltW hau.
Qed.

(** Source for [selected_dyadic_interval_family_succ]: supporting
    last-cell induction for the finite unions in Federer 2.9.20,
    p. 166. The new cell is appended exactly when it lies in S. *)
Lemma selected_dyadic_interval_family_succ (R : realType) (S : set R) (n k : nat) :
  selected_dyadic_interval_family S n k.+1=selected_dyadic_interval_family S n k++
    (if asbool (@dyadic_cell R n k `<=` S)
     then [:: (@dyadic_left R n k, @dyadic_left R n k+@dyadic_step R n)] else [::]).
Proof.
by rewrite /selected_dyadic_interval_family dyadic_interval_family_succ filter_cat /=.
Qed.
