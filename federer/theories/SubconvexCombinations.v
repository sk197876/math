(** Federer (1969), 1.8.1, p. 38: finite weighted combinations of elements
    of S. We temporarily allow nonnegative coefficients with total at most
    one and the empty sum. For sets containing zero this describes the same
    convex hull and handles the zero-dimensional boundary. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import InnerConvex ConcatenatedFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Combinations.
Variable R : realFieldType.
Variable V : lmodType R.
Variable S : set V.

(** Source for [subconvex_combinations]: Federer 1.8.1,
    p. 38, supporting finite-combination predicate. Coefficients are
    nonnegative with total at most one, and n=0 represents zero. *)
Definition subconvex_combinations : set V := fun x =>
  exists n, exists u : 'I_n -> V, exists a : 'I_n -> R,
    (forall i, S (u i)) /\ (forall i, 0 <= a i) /\
    (\sum_i a i <= 1) /\ x = \sum_i a i *: u i.

(** Source for [subconvex_combinations_zero]: Federer 1.8.1,
    p. 38, supporting empty representation of zero, necessary when
    the exterior power has dimension zero. *)
Lemma subconvex_combinations_zero : subconvex_combinations 0.
Proof.
exists 0%N, (fun _ => 0), (fun _ => 0); split.
- move=> i; by have := ltn_ord i; rewrite ltn0.
- split=> //; split; by rewrite big_ord0.
Qed.

(** Source for [subconvex_combinations_include]: Federer 1.8.1,
    p. 38, supporting singleton representation of an element of S. *)
Lemma subconvex_combinations_include x : S x -> subconvex_combinations x.
Proof.
move=> hx; exists 1%N, (fun _ => x), (fun _ => 1).
repeat split=> //; by rewrite big_ord_recr big_ord0 /= ?add0r ?scale1r.
Qed.

(** Source for [subconvex_combinations_convex]: Federer 1.8.1,
    p. 38, supporting convexity of the finite-combination set.
    Concatenate two representations and multiply their weights by
    the two segment coefficients. *)
Theorem subconvex_combinations_convex : is_inner_convex subconvex_combinations.
Proof.
move=> x y [n [u [a [hu [ha [hsa hx]]]]]] [k [v [b [hv [hb [hsb hy]]]]]] t ht0 ht1.
have h1t : 0 <= 1-t by rewrite subr_ge0.
pose w := concatenate_family u v.
pose c := concatenate_family (fun i => (1-t)*a i) (fun i => t*b i).
exists (n+k)%N, w, c; split.
- move=> i; rewrite /w /concatenate_family; case: (split i) => j; [exact: hu | exact: hv].
- split.
  + move=> i; rewrite /c /concatenate_family; case: (split i) => j.
    * exact: mulr_ge0 h1t (ha j).
    * exact: mulr_ge0 ht0 (hb j).
  + split.
    * have hs : (\sum_i c i) = (1-t)*(\sum_i a i)+t*(\sum_i b i).
        rewrite /c big_split_ord !mulr_sumr.
        congr (_ + _); apply: eq_bigr => i _;
          by rewrite ?concatenate_family_l ?concatenate_family_r.
      rewrite hs; have hh := lerD (ler_wpM2l h1t hsa) (ler_wpM2l ht0 hsb).
      by rewrite !mulr1 subrK in hh.
    * rewrite hx hy /c /w concatenate_family_combination.
      rewrite !scaler_sumr; congr (_ + _); apply: eq_bigr => i _; exact: scalerA.
Qed.
End Combinations.
