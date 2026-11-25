(** Supporting finite-union reduction in Federer (1969), 2.9.20, p. 166 We
    reuse the dyadic unions already proved in the project for 2.5.17 instead
    of constructing the open components; see DyadicIntervalFamilies.v for
    this proof-route departure. All mass equalities below use finite
    disjoint additivity, without differentiation or an external measure
    theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import LebesgueLineCharacterisation DyadicIntervalFamilies
  OrderedIntervalFamilyUP MeasureUP MeasureBasic MeasureFiniteAdditivity
  LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_union_succ_selected]: supporting last-cell
    decomposition of the finite approximation used for Federer 2.9.20, p.
    166 The existing half-open cell is added exactly when it lies in S. *)
Lemma dyadic_union_succ_selected (R : realType) (S : set R) (n k : nat) :
  dyadic_union S n k.+1=if asbool (@dyadic_cell R n k `<=` S)
    then dyadic_cell n k `|` dyadic_union S n k else dyadic_union S n k.
Proof.
case: asboolP=> hk; apply/seteqP; split=> x.
- move=> [j [hj hjS hx]]; move: hj; rewrite ltnS leq_eqVlt=> /orP[/eqP hjk|hjk].
  + left; by rewrite -hjk.
  + right; by exists j.
- move=> [hx|[j [hj hjS hx]]].
  + by exists k.
  + exists j; split=> //; exact: ltnW hj.
- move=> [j [hj hjS hx]]; move: hj; rewrite ltnS leq_eqVlt=> /orP[/eqP hjk|hjk].
  + exfalso; apply: hk; by rewrite -hjk.
  + by exists j.
- move=> [j [hj hjS hx]]; exists j; split=> //; exact: ltnW hj.
Qed.

(** Source for [selected_dyadic_family_measure]: supporting exact finite
    mass sum for Federer 2.9.20, p. 166 Half-open cells are disjoint, so
    their mass sum equals the mass of the selected union. No assumption
    about atoms at cell endpoints is required. *)
Lemma selected_dyadic_family_measure (R : realType) (mu : set R -> \bar R)
    (S : set R) (n k : nat) : is_measure mu ->
  (forall j, measure_measurable mu (@dyadic_cell R n j)) ->
  mu (dyadic_union S n k)=\sum_(uv <- selected_dyadic_interval_family S n k) mu `[uv.1,uv.2[.
Proof.
move=> hm hcell; elim: k=> [|k ih].
- have he : dyadic_union S n 0=set0 by apply/seteqP; split=> x // [j []].
  by rewrite he (measure_empty hm) /selected_dyadic_interval_family /dyadic_interval_family /= big_nil.
- rewrite dyadic_union_succ_selected selected_dyadic_interval_family_succ.
  case: asboolP=> hk.
  + have hdis : forall x, @dyadic_cell R n k x -> dyadic_union S n k x -> False.
      move=> x hx [j [hj _ hjx]]; exact: dyadic_cell_disjoint hj hjx hx.
    by rewrite (measure_disjoint_union (hcell k) hdis) ih big_cat big_seq1 addeC.
  + by rewrite cats0 ih.
Qed.

(** Source for [selected_dyadic_family_length]: supporting length sum for
    the finite approximation in Federer 2.9.20, p. 166 Scalar Lebesgue
    measure of each selected half-open cell is its full length. *)
Lemma selected_dyadic_family_length (R : realType) (S : set R) (n k : nat) :
  lebesgue_scalar_measure (dyadic_union S n k)=
    (real_interval_family_length (selected_dyadic_interval_family S n k))%:E.
Proof.
have hm := lebesgue_scalar_is_measure R.
have hr := lebesgue_scalar_borel_regular R.
rewrite (@selected_dyadic_family_measure R _ S n k hm
  (fun j => @dyadic_cell_measurable R (@lebesgue_scalar_measure R) n j hm hr))
  /real_interval_family_length -sumEFin !big_seq.
apply: eq_bigr=> uv huv.
have [j [hjk [heq hS]]] := (selected_dyadic_interval_family_member S n k uv).1 huv.
rewrite heq /=.
have hab : (@dyadic_left R n j<=@dyadic_left R n j+@dyadic_step R n)%R.
  by rewrite lerDl; exact: ltW (@dyadic_step_gt0 R n).
exact (@half_open_interval_measure R (@lebesgue_scalar_measure R)
  (@dyadic_left R n j) (@dyadic_left R n j+@dyadic_step R n)
  hm hr (@lebesgue_scalar_segment R) hab).
Qed.
