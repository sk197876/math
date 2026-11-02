(** Federer (1969), 1.7.3, p. 30: completing the prescribed normalised
    nonzero images to an orthonormal n-family. Capacity is stated by an
    independent n-family, allowing an infinite-dimensional target. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies FiniteIndependence
  OrthonormalCapacityExtension FinitePredicatePartition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [partial_orthonormal_completion]: Federer
    1.7.3, p. 30, supporting extension of the prescribed images
    h(e_i) across the kernel: any partially prescribed orthonormal
    n-family extends if the target has at least n independent vectors. *)
Theorem partial_orthonormal_completion (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (u : 'I_n -> V)
    (hu : finite_independent u) (P : pred 'I_n) (v : 'I_n -> V)
    (hv : forall i, P i -> B (v i) (v i) = 1)
    (hvo : forall i j, i != j -> P i -> P j -> B (v i) (v j) = 0) :
  exists d : 'I_n -> V, orthonormal_family B d /\
    forall i, P i -> d i = v i.
Proof.
pose J := Finite.clone {i : 'I_n | P i} _.
pose K := Finite.clone {i : 'I_n | ~~ P i} _.
pose a := fun i : 'I_#|J| => v (val (enum_val i : J)).
have ha : orthonormal_family B a.
  move=> i j; case: eqP => [->|hne]; first exact: hv (valP (enum_val j : J)).
  apply: hvo; [|exact: valP|exact: valP].
  apply/eqP=> heq; apply: hne; apply: enum_val_inj; exact: val_inj heq.
have hsize : (#|J| + #|K|)%N = n.
  by rewrite predicate_partition_size card_ord.
have hkn : (#|J| <= n)%N by rewrite -hsize; exact: leq_addr.
have [b [hb hba]] := @orthonormal_capacity_extension R V B hB n u hu #|J| a ha hkn.
pose idx := fun i : 'I_n => cast_ord hsize (predicate_partition_rank P i).
have hi : injective idx.
  move=> i j hij; apply: (@predicate_partition_injective (Finite.clone 'I_n _) P).
  apply: val_inj; exact (congr1 val hij).
exists (fun i => b (idx i)); split.
- by move=> i j; rewrite hb (inj_eq hi).
- move=> i hPi.
  have hpos := @predicate_partition_positive (Finite.clone 'I_n _) P (Sub i hPi).
  change (predicate_partition_rank P i = lshift #|K| (enum_rank (Sub i hPi : J))) in hpos.
  have hidx : idx i = widen_ord hkn (enum_rank (Sub i hPi : J)).
    rewrite /idx hpos; exact: val_inj.
  by rewrite hidx hba /a enum_rankK.
Qed.
