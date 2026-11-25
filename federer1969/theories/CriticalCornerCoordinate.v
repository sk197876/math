(** Federer (1969), 3.3.20, pp. 308–309:
    scalar coordinates of the actual inward corner intervals. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra ring.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_corner_coordinate]: supporting lower
    endpoint coordinate of an inward-offset interval in
    the corner pairings of 3.3.20, pp. 308–309.
    The boolean chooses the right rather than left corner. *)
Definition critical_corner_coordinate (R:realType) (r:R) (b:bool) (a:nat):R:=
  if b then 1-(a+1)%:R/r else a%:R/r.

(** Source for [critical_corner_interval_endpoints_unique]:
    supporting uniqueness of the original offset and corner
    from an interval, for the distinct-square certificates
    of 3.3.20, pp. 308–309. The two
    corner strips are separated, and equality of original
    intervals gives equality of their lower endpoints. *)
Lemma critical_corner_interval_endpoints_unique (R:realType) (r:R)
    (b d:bool) (a c:nat):
  0<r ->((a+1)%:R:R)/r<=1/4 ->((c+1)%:R:R)/r<=1/4 ->
  (`[critical_corner_coordinate r b a,critical_corner_coordinate r b a+1/r]:set (real_line_metric R))=
  (`[critical_corner_coordinate r d c,critical_corner_coordinate r d c+1/r]:set (real_line_metric R)) ->
  b=d /\a=c.
Proof.
move=>hr ha hc hEqual.
have hWidth:0<1/r by rewrite divr_gt0.
have hLeft:critical_corner_coordinate r b a<=critical_corner_coordinate r b a+1/r by lra.
have hRight:critical_corner_coordinate r d c<=critical_corner_coordinate r d c+1/r by lra.
have hA:(`[critical_corner_coordinate r b a,critical_corner_coordinate r b a+1/r]:set (real_line_metric R))
    (critical_corner_coordinate r b a) by apply/andP;split=>//;exact:lexx.
have hC:(`[critical_corner_coordinate r d c,critical_corner_coordinate r d c+1/r]:set (real_line_metric R))
    (critical_corner_coordinate r d c) by apply/andP;split=>//;exact:lexx.
rewrite hEqual in hA.
rewrite -hEqual in hC.
move:hA hC=>/andP[hCA _] /andP[hAC _].
change (is_true (critical_corner_coordinate r d c<=critical_corner_coordinate r b a)) in hCA.
change (is_true (critical_corner_coordinate r b a<=critical_corner_coordinate r d c)) in hAC.
have hLow:critical_corner_coordinate r b a=critical_corner_coordinate r d c by apply/eqP;rewrite eq_le hCA hAC.
have hNatA:((a+1)%:R:R)=a%:R+1 by rewrite natrD.
have hNatC:((c+1)%:R:R)=c%:R+1 by rewrite natrD.
have hA0:0<=(a%:R:R)/r by apply:divr_ge0;[exact:ler0n|exact:ltW hr].
have hC0:0<=(c%:R:R)/r by apply:divr_ge0;[exact:ler0n|exact:ltW hr].
have hAQ:(a%:R:R)/r<=1/4 by rewrite hNatA mulrDl mul1r in ha; lra.
have hCQ:(c%:R:R)/r<=1/4 by rewrite hNatC mulrDl mul1r in hc; lra.
clear hEqual hLeft hRight hCA hAC.
case:b hLow=>[|];case:d=>[|] /= hLow;
  rewrite /critical_corner_coordinate /= in hLow.
- split=>//.
  have hSame:((a+1)%:R:R)/r=((c+1)%:R:R)/r by lra.
  have hNZ:r!=0 by rewrite gt_eqF.
  have hSameNat:=congr1 (fun x:R=>x*r) hSame.
  rewrite !divfK // in hSameNat.
  have hCast:(a%:R:R)=c%:R by rewrite hNatA hNatC in hSameNat; lra.
  apply/eqP;by rewrite -(@eqr_nat R) hCast eqxx.
- exfalso;lra.
- exfalso;lra.
- split=>//.
  have hNZ:r!=0 by rewrite gt_eqF.
  have hCast:=congr1 (fun x:R=>x*r) hLow.
  rewrite !divfK // in hCast.
  apply/eqP;by rewrite -(@eqr_nat R) hCast eqxx.
Qed.
