(** Federer (1969), 2.2.17, p. 72, displayed open approximation bound,
    including sets of infinite measure. Source context: ProperMapUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasurePushforward RadonMeasureUP RadonMeasureBounds
  ProperMapUP ProperContinuousClosed ProperOuterNeighborhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radon_open_outer_error_bound]: supporting choice of the open
    source neighborhood for Federer 2.2.17, p. 72 This is the additive-error
    consequence of the Radon infimum law, with infinite-measure sets
    allowed. *)
Lemma radon_open_outer_error_bound (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (A : set X) (epsilon : R) : (0 < epsilon)%R ->
  exists U, open U /\ A `<=` U /\ mu U <= epsilon%:E + mu A.
Proof.
move=> he; case: (ltP (mu A) +oo)=> hfin.
- have hnum : mu A \is a fin_num.
    by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R X mu hm A).
  have hlt : mu A < mu A + epsilon%:E.
    by rewrite -{1}[mu A]adde0 lteD2lE // lte_fin.
  have [U [hU [hAU hu]]] := @radon_outer_strict_approximation R X mu hr A _ hlt.
  exists U; split=> //; split=> //; rewrite addeC; exact: ltW hu.
- have hA : mu A = +oo by apply/eqP; rewrite eq_le hfin leey.
  exists setT; split; first exact: openT.
  split; first by move=> x hx.
  by rewrite hA addeC addye // leey.
Qed.

(** Source for [proper_pushforward_open_outer_bound]: direct displayed bound
    in Federer 2.2.17, p. 72: every B is contained in an open W whose image
    measure is at most epsilon plus the image measure of B. *)
Theorem proper_pushforward_open_outer_bound (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (f : X -> Y) (B : set Y) (epsilon : R) :
  hausdorff_space Y -> locally_compact (@setT Y) -> continuous f -> is_proper_map f ->
  (0 < epsilon)%R -> exists W, open W /\ B `<=` W /\
    measure_pushforward f mu W <= epsilon%:E + measure_pushforward f mu B.
Proof.
move=> hY hl hf hp he.
have [U [hU [hBU hu]]] := @radon_open_outer_error_bound R X mu hm hr (f @^-1` B) epsilon he.
have hclosed := @proper_continuous_map_closed X Y f hY hl hf hp.
have [W [hW [hBW hWU]]] := @proper_outer_open_neighborhood X Y f B U hclosed hU hBU.
exists W; split=> //; split=> //; apply: le_trans _ hu.
exact: (@measure_mono R X mu hm (f @^-1` W) U hWU).
Qed.
