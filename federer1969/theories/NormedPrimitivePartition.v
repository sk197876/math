(** Federer (1969), 3.1.11, pp. 220–221:
    summing primitive increment errors over a tagged
    partition. The scalar cell lengths telescope exactly,
    so the estimate does not depend on the number of cells. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import RealNormUP StieltjesSums StieltjesIntegral NormedStieltjesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_primitive_partition_estimate]:
    the finite telescoping estimate supporting integration
    of a derivative, used in the Taylor proof of
    Federer 3.1.11, pp. 220–221. No
    completeness or existence of an integral is presupposed. *)
Theorem normed_primitive_partition_estimate (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (F D : R->Y) (a b d e : R) (w : seq R) :
  (forall p u q, a<=p -> p<=u -> u<=q -> q<=b -> q-p<d ->
    NY ((q-p)*:D u-(F q-F p))<=e*(q-p)) ->
  is_tagged_partition a b w -> tagged_mesh_lt d w ->
  NY (normed_stieltjes_sum D (fun t=>t) w-(F b-F a))<=e*(b-a).
Proof.
have [n] := ubnP (size w).
elim: n w a=> // n ih [|t [|u [|t' rest]]] a hsize hcell hw hm.
- by case: hw=> [_ [hodd _]].
- have [_ [_ [ht hb]]] := hw; move: ht hb=> /= -> <-.
  by rewrite /= !subrr (real_seminorm_zero hNY.1) mulr0.
- by case: hw=> [_ [hodd _]].
- have [t'' [rest' [he [hat [htu [hut' htail]]]]]] := tagged_partition_tail hw.
  case: he=> ht'' hrest'; subst t'' rest'.
  have hs : (size (t'::rest)<n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
  change (is_true ((t'-t<d)&&tagged_mesh_lt d (t'::rest))) in hm.
  have /andP [hwidth hmesh] := hm.
  have ht'b : t'<=b.
    by have /andP [_ hh] := tagged_partition_points_bounds htail (tagged_partition_a_mem htail).
  have hat' : a<=t' by rewrite hat; exact: le_trans htu hut'.
  have htailcell p v q : t'<=p -> p<=v -> v<=q -> q<=b -> q-p<d ->
      NY ((q-p)*:D v-(F q-F p))<=e*(q-p).
    move=> htp hpv hvq hqb hpq.
    exact: hcell p v q (le_trans hat' htp) hpv hvq hqb hpq.
  have hrest := ih (t'::rest) t' hs htailcell htail hmesh.
  have hat0 : a<=t by rewrite hat.
  have hfirst := hcell t u t' hat0 htu hut' ht'b hwidth.
  have hinc : F b-F a=(F t'-F a)+(F b-F t') by rewrite [RHS]addrC addrA subrK.
  change (NY ((t'-t)*:D u+normed_stieltjes_sum D (fun t=>t) (t'::rest)-
    (F b-F a))<=e*(b-a)).
  rewrite hinc opprD addrACA.
  rewrite hat.
  apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  apply: le_trans (lerD hfirst hrest) _.
  have hid : e*(t'-t)+e*(b-t')=e*(b-t) by ring.
  by rewrite hid.
Qed.
