(** Federer (1969), 3.2.35, p. 271:
    existence of the finite Minkowski gauge under
    absorption, using the complete real infimum background.
    The witness remains local to the existence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import MinkowskiGaugeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [minkowski_gauge_exists]: supporting
    existence for the defining infimum of Federer
    3.2.35, p. 271. Every positive rescaling
    set is nonempty by the displayed absorption
    hypothesis and bounded below by zero. The
    complete scalar infimum therefore satisfies the
    independent laws. Absorption of open sets containing
    zero is proved separately; no globally selected
    gauge or project axiom is introduced. *)
Theorem minkowski_gauge_exists (R:realType) (V:lmodType R) (S:set V):
  (forall x:V,exists t:R,0<t /\S (t^-1*:x)) ->
  exists g:V->R,is_minkowski_gauge S g.
Proof.
move=>hAbsorb; pose T x:set R:=[set t|0<t /\S (t^-1*:x)].
have hT x:T x!=set0 by have [t ht]:=hAbsorb x; exists t.
have hLower x:has_lbound (T x).
  exists 0=>t [ht _]; exact:ltW ht.
exists (fun x=>inf (T x)); constructor.
- move=>x t ht hS; apply:(ge_inf (hLower x)); by split.
- move=>x c hb; apply:(lb_le_inf (hT x)).
  by move=>t [ht hS]; exact:hb t ht hS.
Qed.
