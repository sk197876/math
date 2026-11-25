(** Federer (1969), 1.10.5, p. 47: supporting order and topology argument
    for the norm of a power of a one-form. Raising nonnegative values to a
    positive integral power commutes with their supremum, also when it is
    infinite. This is a local proof from the supremum specification, real
    power continuity and closure; no theorem about operator norms is
    imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nonnegative_extended_power_monotone]: Federer
    1.10.5, p. 47, supporting monotonicity of nonnegative
    extended powers, proved by multiplication induction. *)
Lemma nonnegative_extended_power_monotone (R : realType) (x y : \bar R) n :
  (0<=x)%E -> (x<=y)%E -> (x^+n<=y^+n)%E.
Proof.
move=> hx hxy; have hy := le_trans hx hxy.
elim: n=> [|n ih]; first by rewrite !expe0.
rewrite !expeS; apply: lee_pmul=> //; exact: expe_ge0.
Qed.

(** Source for [finite_extended_supremum_closure]: Federer
    1.10.5, p. 47, supporting finite supremum approximation:
    a finite least upper bound belongs to the closure of its nonempty
    value set. This is general real topology. *)
Lemma finite_extended_supremum_closure (R : realType) (S : set R) a :
  S !=set0 -> is_extended_supremum S a%:E -> closure S a.
Proof.
move=> hne hc.
have hu : ubound S a.
  move=> x hx; have hh := extended_supremum_upper hc hx.
  by rewrite lee_fin in hh.
have hs : has_sup S by split=> //; exists a.
have he : sup S=a.
  apply/eqP; rewrite eq_le; apply/andP; split; first exact: ge_sup hne hu.
  have hh := @extended_supremum_least R S a%:E hc (sup S)%:E
    (fun x hx => lee_tofin (@sup_upper_bound R S hs x hx)).
  by rewrite lee_fin in hh.
rewrite -he; apply: closure_sup=> //; by exists a.
Qed.

(** Source for [real_power_closed_sublevel]: Federer 1.10.5,
    p. 47, supporting continuity argument: the set where a real
    integral power is at most a fixed bound is closed. *)
Lemma real_power_closed_sublevel (R : realType) n (b:R) :
  closed [set x : R | x^+n<=b].
Proof.
have hcont : continuous (fun x:R => x^+n).
  elim: n=> [|n ih] x; first exact: cvg_cst.
  have he : (fun y:R=>y^+n.+1) = (fun y:R=>y*y^+n).
    by apply: funext=> y; rewrite exprS.
  rewrite he /=.
  exact: cvgM cvg_id (ih x).
change (closed ((fun x:R=>x^+n) @^-1` [set y:R|y<=b])).
apply: preimage_closed; last exact: closed_le.
by move=> x _; exact: hcont.
Qed.

(** Source for [extended_supremum_power_least]: Federer
    1.10.5, p. 47, supporting supremum-of-powers principle.
    Any upper bound of all positive integral powers of nonnegative
    values also bounds the same power of their extended supremum. *)
Theorem extended_supremum_power_least (R : realType) (S : set R)
    (c : \bar R) (hc : is_extended_supremum S c)
    (hne : S !=set0) (hpos : forall x, S x -> 0<=x)
    n (hn : (0<n)%N) (d : \bar R) :
  (forall x, S x -> ((x^+n)%:E<=d)%E) -> (c^+n<=d)%E.
Proof.
move=> hb.
have hc0 : (0<=c)%E.
  apply: (@extended_supremum_nonnegative R S c hc).
  have [x hx] := hne; exists x; by split=> //; exact: hpos.
case: d hb=> [b| |] hb; [|exact: leey|].
- have hbc : (c <= (Num.max 1 b)%:E)%E.
    apply: (@extended_supremum_least R S c hc)=> x hx; rewrite lee_fin.
    rewrite le_max; apply/orP.
    case: (leP x 1)=> h1; first by left.
    right.
    have hh := hb x hx; rewrite lee_fin in hh.
    exact: le_trans (ler_eXnr hn (ltW h1)) hh.
  case: c hc hc0 hbc=> [a| |] hc hc0 hbc; last 2 first.
  + by rewrite leye_eq in hbc.
  + by rewrite leeNy_eq in hc0.
  rewrite -EFin_expe lee_fin.
  have ha := @finite_extended_supremum_closure R S a hne hc.
  have hsub : S `<=` [set x:R|x^+n<=b].
    move=> x hx; have hh:=hb x hx; by rewrite lee_fin in hh.
  have hh := closureS hsub ha.
  by rewrite -(proj1 (closure_id _) (@real_power_closed_sublevel R n b)) in hh.
- have [x hx] := hne; have hh := hb x hx.
  by rewrite leeNy_eq in hh.
Qed.
