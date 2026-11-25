(** Federer (1969), 3.4.8(1), p. 326:
    the original finite basis gives an auxiliary inclusion
    of prefix coordinates. The finite sum proves existence;
    downstream arguments use only its independent basis laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates AnalyticPrefixCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_prefix_section_exists]: the original
    basis determines the coordinate inclusion used for
    the subring in 3.4.8(1),(5), pp. 326, 328.
    Empty prefixes and their zero maps remain. *)
Theorem analytic_prefix_section_exists (R:realType) (X:lmodType R) n
    (e:'I_n->X) j (hjn:(j<=n)%N):
  exists S:Hom (R_n R j) X,is_analytic_prefix_section e hjn S.
Proof.
pose f (z:R_n R j):X:=\sum_(i<j) z i*:e (widen_ord hjn i).
have hLinear:linear f.
  move=>a x y;rewrite /f scaler_sumr -big_split.
  apply:eq_bigr=>i _;by rewrite !ffunE scalerDl scalerA.
exists (@HomMap R (R_n R j) X f (introT (asboolP _) hLinear))=>i.
change (f (@coordinate_basis R j i)=e (widen_ord hjn i)).
rewrite /f (bigD1 i) //= /coordinate_basis ffunE eqxx scale1r.
have hRest:(\sum_(k<j|k!=i) (if k==i then (1:R) else 0)*:e (widen_ord hjn k))=0.
  apply:big1=>k hk;by rewrite (negbTE hk) scale0r.
under eq_bigr do rewrite ffunE.
by rewrite hRest addr0.
Qed.
