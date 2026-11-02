(** Federer (1969), 3.1.20, p. 233: inclusion of derivative
    images implies the corresponding rank inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom LinearRankUP LinearRankAtLeast.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [linear_rank_image_inclusion]: supporting
    image Df(x) subset image Df[f(x)] in Federer 3.1.20,
    p. 233. The image inclusion bounds the first rank by the
    second, independently of a matrix representation. *)
Lemma linear_rank_image_inclusion (K:fieldType) (X Y Z:lmodType K)
    (L:Hom X Z) (M:Hom Y Z) r s : has_linear_rank L r -> has_linear_rank M s ->
  (forall x,exists y,M y=L x) -> (r<=s)%N.
Proof.
move=>hL hM hincl.
have [e he]:=(linear_rank_at_leastP r hL).2 (leqnn r).
have [d hd]:=choice (fun i:'I_r=>hincl (e i)).
apply: (linear_rank_at_leastP r hM).1.
exists d=>c hc; apply: he.
have hs:(\sum_i c i*:L (e i))=\sum_i c i*:M (d i).
  apply: eq_bigr=>i _; by rewrite hd.
by rewrite hs.
Qed.
