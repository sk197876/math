(** Federer (1969), 3.4.5, p. 320: local
    vanishing is independent of the original function and set
    representatives and is closed under the ideal operations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets topology.
From Federer Require Import LocalGermUP GermVanishingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Vanishing.
Variable X:topologicalType.
Variable A:comNzRingType.
Variable a:X.

(** Source for [vanishes_near_representative_independence]:
    the ideal is determined by the two germs, 3.4.5,
    p. 320. Intersect the three actual neighbourhoods. *)
Lemma vanishes_near_representative_independence (S T:set X) (f g:X->A):
  locally_equal_at a S T ->locally_equal_at a f g ->
  vanishes_near_on a S f ->vanishes_near_on a T g.
Proof.
move=>[U [hU [ha hST]]] [V [hV [hb hFG]]] [W [hW [hc hZero]]].
exists (U `&` (V `&` W));split;first exact:openI hU (openI hV hW).
split;first by split;last split.
move=>x hx [hu [hv hw]].
rewrite -(hFG x hv);apply:hZero;last exact:hw.
by rewrite (hST x hu).
Qed.

(** Source for [vanishes_near_zero]: the zero function
    is in every set ideal, 3.4.5, p. 320. *)
Lemma vanishes_near_zero (S:set X):vanishes_near_on a S (fun _=>0:A).
Proof. exists setT;split;first exact:openT. by split. Qed.

(** Source for [vanishes_near_add]: local vanishing is
    closed under functional addition, 3.4.5, p. 320. *)
Lemma vanishes_near_add (S:set X) (f g:X->A):
  vanishes_near_on a S f ->vanishes_near_on a S g ->
  vanishes_near_on a S (fun x=>f x+g x).
Proof.
move=>[U [hU [ha hF]]] [V [hV [hb hG]]].
exists (U `&` V);split;first exact:openI hU hV.
split;first by split.
by move=>x hx [hu hv];rewrite (hF x hx hu) (hG x hx hv) add0r.
Qed.

(** Source for [vanishes_near_opp]: local vanishing is
    closed under functional negation, 3.4.5, p. 320. *)
Lemma vanishes_near_opp (S:set X) (f:X->A):
  vanishes_near_on a S f ->vanishes_near_on a S (fun x=>-f x).
Proof.
move=>[U [hU [ha hF]]];exists U;split;first exact:hU.
split;first exact:ha.
by move=>x hx hu;rewrite (hF x hx hu) oppr0.
Qed.

(** Source for [vanishes_near_mul]: multiplication by any
    representative preserves local vanishing, 3.4.5, p. 320. *)
Lemma vanishes_near_mul (S:set X) (f g:X->A):
  vanishes_near_on a S g ->vanishes_near_on a S (fun x=>f x*g x).
Proof.
move=>[U [hU [ha hG]]];exists U;split;first exact:hU.
split;first exact:ha.
by move=>x hx hu;rewrite (hG x hx hu) mulr0.
Qed.
End Vanishing.
