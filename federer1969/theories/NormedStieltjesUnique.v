(** Federer (1969), 3.1.11, pp. 220–221:
    the vector-valued Stieltjes limit in the Taylor
    formula is unique in any normed target. The
    argument uses fine tagged partitions and norm separation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import RealNormUP StieltjesSums StieltjesIntegral NormedStieltjesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_stieltjes_integral_unique]:
    uniqueness of the norm limit underlying the integral
    in Federer 3.1.11, pp. 220–221. Neither
    completeness nor finite dimension is needed. *)
Theorem normed_stieltjes_integral_unique (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY) (f : R->Y) (g : R->R)
    (a b : R) (u v : Y) :
  has_normed_stieltjes_integral NY f g a b u ->
  has_normed_stieltjes_integral NY f g a b v -> u=v.
Proof.
move=> [hab hu] [_ hv]; apply: contrapT=> hne.
have hdiff : 0<NY (u-v).
  rewrite (real_norm_positive hNY.1 hNY.2) subr_eq0; exact/eqP.
pose e := NY (u-v)/3.
have he : 0<e by rewrite /e divr_gt0 // ltr0n.
have [r [hr hru]] := hu e he.
have [s [hs hsv]] := hv e he.
have hmin : 0<Num.min r s by rewrite lt_min hr hs.
have [n hn] := uniform_mesh_small hab hmin.
pose w := uniform_partition a b n.
have hw : is_tagged_partition a b w := uniform_partition_is n hab.
have hm : tagged_mesh_lt (Num.min r s) w.
  exact: uniform_partition_mesh (hn n (leqnn n)).
have hmr : Num.min r s<=r by rewrite ge_min lexx.
have hms : Num.min r s<=s by rewrite ge_min lexx orbT.
have h1 := hru w hw (tagged_mesh_lt_le hmr hm).
have h2 := hsv w hw (tagged_mesh_lt_le hms hm).
pose z := normed_stieltjes_sum f g w.
have hid : u-v=(u-z)+(z-v) by rewrite addrA subrK.
have htri := real_seminorm_triangle hNY.1 (u-z) (z-v).
rewrite -hid (real_seminorm_subtract hNY.1 u z) in htri.
rewrite /e in h1 h2; nra.
Qed.
