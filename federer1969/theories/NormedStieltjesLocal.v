(** Federer (1969), 3.2.13, p. 250: localizing
    the internal fundamental theorem to a positive
    segment for the Gamma recurrence. Tagged sums
    depend only on the integrand at their actual
    tags; outside-segment extensions do not change them. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import NormedStieltjesUP StieltjesSums StieltjesIntegral StieltjesSubstitution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_stieltjes_sum_list_agreement]: supporting
    localization of the tagged sums of 2.5.17,
    p. 110, for Gamma integration by parts
    in Federer 3.2.13, p. 250. Only
    values on the actual finite list are required. *)
Lemma normed_stieltjes_sum_list_agreement (R:realType) (Y:lmodType R)
    (f q:R->Y) (g:R->R) (w:seq R):
  (forall t,t\in w ->f t=q t) ->
  normed_stieltjes_sum f g w=normed_stieltjes_sum q g w.
Proof.
have [n]:=ubnP (size w).
elim:n w=>[//|n ih] [|t [|u [|z rest]]] hSize hAgree=>//.
have hSmall:(size (z::rest)<n)%N by move:hSize; rewrite /= ltnS; exact:ltnW.
have hTag:f u=q u.
  apply:hAgree; by rewrite !in_cons eqxx orbT.
have hTail:forall x,x\in z::rest ->f x=q x.
  move=>x hx; apply:hAgree.
  rewrite in_cons; apply/orP; right; rewrite in_cons; apply/orP; right; exact hx.
change ((g z-g t)*:f u+normed_stieltjes_sum f g (z::rest)=
  (g z-g t)*:q u+normed_stieltjes_sum q g (z::rest)).
by rewrite hTag (ih _ hSmall hTail).
Qed.

(** Source for [normed_stieltjes_integral_segment_agreement]:
    replacement by a continuous segment extension in
    the Gamma recurrence, Federer 3.2.13, p. 250,
    using only the tagged-sum laws of 2.5.17,
    pp. 110–111. Agreement is required on
    the actual closed segment, not globally. *)
Lemma normed_stieltjes_integral_segment_agreement (R:realType) (Y:lmodType R)
    (NY:Y->R) (f q:R->Y) (g:R->R) (a b:R) (v:Y):
  (forall t,a<=t<=b ->f t=q t) ->
  has_normed_stieltjes_integral NY f g a b v ->
  has_normed_stieltjes_integral NY q g a b v.
Proof.
move=>hEq [hab hI]; split=>// e he.
have [d [hd hBound]]:=hI e he.
exists d; split=>// w hw hMesh.
have hList:forall t,t\in w ->f t=q t.
  move=>t ht; exact (hEq t (tagged_partition_mem_bounds hw ht)).
rewrite -(@normed_stieltjes_sum_list_agreement R Y f q g w hList).
exact:hBound w hw hMesh.
Qed.
