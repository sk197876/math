(** Federer (1969), 3.1.11, pp. 220–221:
    a cellwise comparison of vector Stieltjes sums.
    This supports the equivalent forms of the
    Taylor integral using exactly the tagged partitions
    of 2.5.17, pp. 110–111. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import RealNormUP StieltjesSums StieltjesIntegral NormedStieltjesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_stieltjes_partition_comparison]:
    cell errors bounded by e times cell length
    sum to at most e times the total length,
    supporting the change of integrator in Federer
    3.1.11, pp. 220–221. *)
Theorem normed_stieltjes_partition_comparison (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (f v : R->Y) (g r : R->R) (a b d e : R) (w : seq R) :
  (forall p u q, a<=p -> p<=u -> u<=q -> q<=b -> q-p<d ->
    NY ((g q-g p)*:f u-(r q-r p)*:v u)<=e*(q-p)) ->
  is_tagged_partition a b w -> tagged_mesh_lt d w ->
  NY (normed_stieltjes_sum f g w-normed_stieltjes_sum v r w)<=e*(b-a).
Proof.
have [n] := ubnP (size w).
elim: n w a=> // n ih [|t [|u [|t' rest]]] a hsize hcell hw hm.
- by case: hw=> [_ [hodd _]].
- have [_ [_ [ht hb]]] := hw; move: ht hb=> /= -> <-.
  by rewrite /= subrr (real_seminorm_zero hNY.1) subrr mulr0.
- by case: hw=> [_ [hodd _]].
- have [t'' [rest' [he [hat [htu [hut' htail]]]]]] := tagged_partition_tail hw.
  case: he=> ht'' hrest'; subst t'' rest'.
  have hs : (size (t'::rest)<n)%N by move: hsize; rewrite /= ltnS; exact: ltnW.
  change (is_true ((t'-t<d)&&tagged_mesh_lt d (t'::rest))) in hm.
  have /andP [hwidth hmesh] := hm.
  have ht'b : t'<=b.
    by have /andP [_ hh] := tagged_partition_points_bounds htail (tagged_partition_a_mem htail).
  have hat' : a<=t' by rewrite hat; exact: le_trans htu hut'.
  have htailcell p z q : t'<=p -> p<=z -> z<=q -> q<=b -> q-p<d ->
      NY ((g q-g p)*:f z-(r q-r p)*:v z)<=e*(q-p).
    move=> htp hpz hzq hqb hpq.
    exact: hcell p z q (le_trans hat' htp) hpz hzq hqb hpq.
  have hrest := ih (t'::rest) t' hs htailcell htail hmesh.
  have hat0 : a<=t by rewrite hat.
  have hfirst := hcell t u t' hat0 htu hut' ht'b hwidth.
  change (NY (((g t'-g t)*:f u+normed_stieltjes_sum f g (t'::rest))-
    ((r t'-r t)*:v u+normed_stieltjes_sum v r (t'::rest)))<=e*(b-a)).
  rewrite opprD addrACA hat.
  apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  apply: le_trans (lerD hfirst hrest) _.
  have hid : e*(t'-t)+e*(b-t')=e*(b-t) by ring.
  by rewrite hid.
Qed.

(** Source for [normed_stieltjes_integral_transfer]:
    asymptotically equal tagged sums have the same
    integral value, supporting the ordinary/Stieltjes
    equivalence used in Federer 3.1.11,
    pp. 220–221. No integral is assigned
    until its tagged-sum limit is proved. *)
Theorem normed_stieltjes_integral_transfer (R : realType)
    (Y : lmodType R) (NY : Y->R) (hNY : is_real_norm NY)
    (f v : R->Y) (g r : R->R) (a b : R) (y : Y) :
  (forall e : R, 0<e -> exists d : R, 0<d /\
    forall w, is_tagged_partition a b w -> tagged_mesh_lt d w ->
      NY (normed_stieltjes_sum f g w-normed_stieltjes_sum v r w)<e) ->
  has_normed_stieltjes_integral NY v r a b y ->
  has_normed_stieltjes_integral NY f g a b y.
Proof.
move=> hclose [hab hi]; split; first exact hab.
move=> e he; have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [s [hs hcs]] := hclose _ he2.
have [t [ht hit]] := hi _ he2.
exists (Num.min s t); split; first by rewrite lt_min hs ht.
move=> w hw hm.
have hms : Num.min s t<=s by rewrite ge_min lexx.
have hmt : Num.min s t<=t by rewrite ge_min lexx orbT.
have h1 := hcs w hw (tagged_mesh_lt_le hms hm).
have h2 := hit w hw (tagged_mesh_lt_le hmt hm).
have hid : normed_stieltjes_sum f g w-y=
    (normed_stieltjes_sum f g w-normed_stieltjes_sum v r w)+
    (normed_stieltjes_sum v r w-y).
  by rewrite addrA subrK.
rewrite hid; apply: le_lt_trans (real_seminorm_triangle hNY.1 _ _) _.
have hb := ltrD h1 h2.
have heq : e/2+e/2=e by lra.
by rewrite heq in hb.
Qed.
