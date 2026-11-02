(** Federer (1969), 2.10.28(4), pp. 192–193: public equal-cost radius and
    the spacing formula (d-s)/(n-1). Expose the chosen radius only through
    its opaque specification; derive strict separation and endpoint recovery
    without computing through the construction. Source context:
    CantorSplitRadiusUP.v. *)
(** Federer 2.10.28, pp. 192–193: source context and the abstract laws are
    recorded in the corresponding specification module. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ConcaveIntervalGaugeUP CantorSplitRadiusUP CantorSplitRadiusSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [cantor_split_radius]: direct
    equal-cost child length in 2.10.28(4),
    p. 192, using the proved opaque witness. *)
Definition cantor_split_radius (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (d : R) (n : nat) (hd : 0<d) (hn : (2<=n)%N) :=
  @CantorSplitRadius.value R h hg d n hd hn.

(** Source for [cantor_split_radius_specification]:
    direct bounds and cost for s in
    2.10.28(4), p. 192, from its
    abstract sealed interface. *)
Lemma cantor_split_radius_specification (R : realType) (h : R -> R) (hg : is_concave_interval_gauge h)
    (d : R) (n : nat) (hd : 0<d) (hn : (2<=n)%N) :
  is_cantor_split_radius h d n (@cantor_split_radius R h hg d n hd hn).
Proof. exact: CantorSplitRadius.laws. Qed.

(** Source for [cantor_split_radius_proof_independent]:
    supporting independence of witness proofs in
    2.10.28(4), p. 192. Uniqueness follows
    from the gauge laws, not the selected body. *)
Lemma cantor_split_radius_proof_independent (R : realType) (h : R -> R)
    (hg hg' : is_concave_interval_gauge h) d n hd hd' hn hn' :
  @cantor_split_radius R h hg d n hd hn = @cantor_split_radius R h hg' d n hd' hn'.
Proof.
exact: (@cantor_split_radius_unique R h hg d n _ _
  (@cantor_split_radius_specification R h hg d n hd hn)
  (@cantor_split_radius_specification R h hg' d n hd' hn')).
Qed.

(** Source for [cantor_split_spacing]: direct
    t=(diam J-s)/(n-1) in 2.10.28(4),
    p. 192. The child radius is specified
    separately; no claim is made at n<2. *)
Definition cantor_split_spacing (R : realType) (d : R) (n : nat) (s : R) :=
  (d-s)/(n%:R-1).

(** Source for [cantor_split_spacing_strict]: direct t>s conclusion of
    2.10.28(4), p. 192, from the strict bound s<d/n. *)
Lemma cantor_split_spacing_strict (R : realType) (h : R -> R) d n s :
  (2<=n)%N -> is_cantor_split_radius h d n s -> s<cantor_split_spacing d n s.
Proof.
move=> hn hs.
have hN1 : (1<n%:R :> R) by rewrite ltr1n.
have hN : (0<n%:R :> R) := lt_trans ltr01 hN1.
have hden : (0<n%:R-1 :> R) by rewrite subr_gt0.
have hh := (cantor_split_radius_bounds hs).2.
rewrite ltr_pdivlMr // in hh.
rewrite /cantor_split_spacing ltr_pdivlMr //; lra.
Qed.

(** Source for [cantor_split_last_endpoint]: supporting
    equality (n-1)t+s=d in the interval
    formula of 2.10.28(4), p. 192.
    It places the last child's right endpoint
    exactly at the parent's right endpoint. *)
Lemma cantor_split_last_endpoint (R : realType) (d : R) n s : (2<=n)%N ->
  (n%:R-1)*cantor_split_spacing d n s+s=d.
Proof.
move=> hn; have hden : (0<n%:R-1 :> R) by rewrite subr_gt0 ltr1n.
rewrite /cantor_split_spacing mulrC divfK ?gt_eqF //; lra.
Qed.
