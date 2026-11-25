(** Federer (1969), 3.4.5, p. 321: finite
    sparse coefficient sums supporting the actual transverse
    Taylor remainder calculation in the cited example. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Selection.
Variable V:zmodType.

(** Source for [finite_ordinal_delta_sum]: a single
    original scalar-index coefficient is selected exactly when
    it lies inside the finite range, supporting
    3.4.5, p. 321. Empty ranges are retained. *)
Lemma finite_ordinal_delta_sum (N k:nat) (F:nat->V):
  (\sum_(i<N) if ((i:nat)==k)%N then F i else 0)=if (k<N)%N then F k else 0.
Proof.
case hk:(k<N)%N.
- pose q:'I_N:=Ordinal hk.
  rewrite (bigD1 q) //=.
  have hRest:(\sum_(i<N | i!=q) if ((i:nat)==k)%N then F i else 0)=0.
    apply:big1=>i hi.
    have hNot:((i:nat)!=k)%N by move:hi;rewrite -val_eqE.
    by rewrite (negbTE hNot).
  by rewrite hRest addr0 /q /= ?eqxx.
- apply:big1=>i _.
  have hNot:((i:nat)!=k)%N.
    apply/eqP=>hEqual;have hBound:=ltn_ord i;by rewrite hEqual hk in hBound.
  by rewrite (negbTE hNot).
Qed.

(** Source for [finite_rectangular_delta_sum]: a finite
    two-coordinate coefficient sum selects its original index
    precisely when both bounds hold, supporting the surface
    coefficient calculation in 3.4.5, p. 321. *)
Theorem finite_rectangular_delta_sum (N M k l:nat) (F:nat->nat->V):
  (\sum_(i<N) \sum_(j<M) if (((i:nat)==k)&&((j:nat)==l))%N then F i j else 0)=
    if ((k<N)&&(l<M))%N then F k l else 0.
Proof.
have hInner (i:nat):(\sum_(j<M) if (((i:nat)==k)&&((j:nat)==l))%N then F i j else 0)=
    if ((i:nat)==k)%N then (if (l<M)%N then F i l else 0) else 0.
  case hI:((i:nat)==k)%N=>/=.
  - exact:finite_ordinal_delta_sum.
  - exact:big1 (fun j _=>erefl _).
have hOuter:(\sum_(i<N) \sum_(j<M) if (((i:nat)==k)&&((j:nat)==l))%N then F i j else 0)=
    \sum_(i<N) if ((i:nat)==k)%N then (if (l<M)%N then F i l else 0) else 0.
  by apply:eq_bigr=>i _;rewrite hInner.
have hSelection:=@finite_ordinal_delta_sum N k (fun i:nat=>if (l<M)%N then F i l else 0).
rewrite hOuter hSelection.
by case:(k<N)%N;case:(l<M)%N.
Qed.
End Selection.
