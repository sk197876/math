(** Federer (1969), 2.2.16, p. 71, metric base-cardinality step. A dense set
    times the natural scale indices is Ulam whenever the dense set is Ulam.
    This uses the proved union property 2.1.6(1), p. 58, rather than
    claiming that a finite dense set and a countably indexed base have the
    same cardinality. No new infinite-cardinal arithmetic is needed. *)
From mathcomp Require Import all_boot classical_sets cardinality reals.
From Federer Require Import CardinalInjection UlamCardinalUP UlamCountable UlamUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [ulam_set_times_naturals]: supporting cardinal
    bound for the metric base in Federer 2.2.16,
    p. 71. The product is a countable union of
    slices, each injecting into the original Ulam set. This
    includes finite and empty dense sets without a cardinal-equality claim. *)
Theorem ulam_set_times_naturals (R : realType) (X : choiceType) (D : set X) :
  is_ulam_set R D -> is_ulam_set R (D `*` (@setT nat)).
Proof.
move=> hu.
pose F n : set (X * nat) := [set p | D p.1 /\ p.2 = n].
have he : D `*` (@setT nat) = \bigcup_n F n.
  apply/seteqP; split.
  - move=> p [hp _]; exists p.2; first exact Logic.I; by split.
  - move=> p [n _ [hp _]]; by split.
have hslice n : is_ulam_set R (F n).
  have hcard : F n #<= D.
    refine (@cardinal_bound_of_injection [the choiceType of (X * nat)%type] X (F n) D (fun p => p.1) _ _).
    - by move=> p [hp _].
    - move=> p q hp hq heq.
      have [hpD hpn] : F n p := set_mem hp.
      have [hqD hqn] : F n q := set_mem hq.
      apply: (@injective_projections X nat p q heq); by rewrite hpn hqn.
  exact (@ulam_set_downward R [the choiceType of (X * nat)%type] X (F n) D hcard hu).
have hindex : is_ulam_set R (@setT nat).
  apply: ulam_set_countable; exact: countableP.
have hh := @ulam_set_union R _ [the choiceType of (X * nat)%type]
  (@setT nat) F hindex (fun n _ => hslice n).
rewrite -he in hh; exact hh.
Qed.
