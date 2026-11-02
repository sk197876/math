(** Federer (1969), 2.10.28(4), proof p. 193: supporting finite-index
    extrema and the bound on the number of child indices between their first
    and last members. These are finite set-theory facts, not additional
    hypotheses of the geometric construction. The additional constant-three
    clipped estimate is in Federer, not that. *)
From mathcomp Require Import all_boot all_order.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope nat_scope.

(** Source for [finite_ordinal_span_card]: supporting
    cardinality bound for indices lying between
    a and b in 2.10.28(4), p. 193.
    Inject the selected indices into the
    ordinal of length b-a+1; the empty
    selected set remains included. *)
Lemma finite_ordinal_span_card n (P : pred 'I_n) a b :
  (forall i, P i -> a<=i /\ i<=b) -> #|P|<=b-a+1.
Proof.
move=> hbound.
pose T := [the finType of {i : 'I_n | P i}].
have hfbound (x : T) : val (val x)-a<b-a+1.
  have [hlo hhi] := hbound (val x) (valP x).
  rewrite addn1 ltnS; exact (@leq_sub2r a (val (val x)) b hhi).
pose f (x : T) : 'I_(b-a+1) := Ordinal (hfbound x).
have hf : injective f.
  move=> x y hxy.
  have [hax hxb] := hbound (val x) (valP x).
  have [hay hyb] := hbound (val y) (valP y).
  have he : val (val x)-a=val (val y)-a := congr1 val hxy.
  have hh := congr1 (fun k=>k+a) he.
  rewrite !subnK // in hh.
  apply: val_inj; apply: val_inj; exact hh.
have hh := @leq_card T [the finType of 'I_(b-a+1)] f hf.
by rewrite card_sub card_ord in hh.
Qed.

(** Source for [finite_ordinal_extremes]: supporting
    first and last selected child indices
    in 2.10.28(4), p. 193. A
    nonempty finite index set attains both
    extrema; no sorted enumeration is assumed. *)
Lemma finite_ordinal_extremes n (P : pred 'I_n) :
  (exists i, P i) -> exists a b : 'I_n,
    P a /\ P b /\ forall i, P i -> a<=i /\ i<=b.
Proof.
move=> [i0 hi0].
have [a ha hmin] := @arg_minP _ _ [the finType of 'I_n] i0 P (fun i=>val i) hi0.
have [b hb hmax] := @arg_maxP _ _ [the finType of 'I_n] i0 P (fun i=>val i) hi0.
exists a,b; split=> //; split=> // i hi; split; [exact: hmin i hi | exact: hmax i hi].
Qed.
