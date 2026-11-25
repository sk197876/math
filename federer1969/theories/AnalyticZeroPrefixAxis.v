(** Federer (1969), 3.4.8(11), p. 333:
    once the earlier coordinates vanish,
    the next prefix lies on its
    last coordinate axis. This supporting identity
    follows from the original projection laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates AnalyticPrefixCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_zero_prefix_axis]:
    the triangular coordinate step in
    the m=0 proof of 3.4.8(11),
    p. 333. Keep the original next
    coordinate and actual prefix projection. *)
Lemma analytic_zero_prefix_axis (R:realType) (X:lmodType R) n
    (omega:'I_n->Hom X R^o) (j:'I_n)
    (P:Hom X (R_n R (j:nat).+1)):
  is_analytic_prefix_projection omega (ltn_ord j) P ->
  forall x,(forall i:'I_n,(i<j)%N ->omega i x = 0) ->
  P x = (omega j x)*:@coordinate_basis R (j:nat).+1 ord_max.
Proof.
move=>hP x hPrevious;apply/ffunP=>i.
rewrite hP /coordinate_basis !ffunE.
change (omega (widen_ord (ltn_ord j) i) x = omega j x*(if i==ord_max then 1 else 0)).
case:(eqVneq i ord_max)=>[hLast|hEarlier].
- rewrite hLast /=.
  have hIndex:widen_ord (ltn_ord j) (ord_max:'I_(j:nat).+1) = j by apply:val_inj.
  by rewrite hIndex mulr1.
- rewrite mulr0.
  apply:hPrevious.
  have hSmall:(i<j)%N.
    rewrite ltn_neqAle;apply/andP;split;last exact:ltn_ord i.
    by move:hEarlier;rewrite -val_eqE /=.
  exact:hSmall.
Qed.
