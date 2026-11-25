(** Federer (1969), 1.10.5, p. 48: supporting list form
    of the compact extremal-tuple argument. Lists make permutations and
    replacement of two entries explicit, while all form evaluations remain
    those of the original symmetric multilinear map. The source context
    and the local nature of these intermediate claims are recorded in
    HilbertFormCompactness.v and SymmetricFormListSlots.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  LinearBasis SymmetricForms SymmetricFormWords RealNormUP SymmetricOperatorNormUP
  SymmetricOperatorNorm SymmetricFormListSlots HilbertFormCompactness UnitProductFactors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Maximum.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation N := (inner_norm hB).
Variable m : nat.
Variable f : S_m V R^o m.
Local Notation F := (sform_words f).

(** Source for [finite_hilbert_word_secondary_maximum]: Federer
    1.10.5, p. 48, supporting passage from a compact tuple
    maximum to a list of exactly m entries. It preserves both the
    absolute form maximum and the secondary maximum of the sum length. *)
Theorem finite_hilbert_word_secondary_maximum n (e : 'I_n -> V) (he : is_basis e) :
  exists s : seq V, size s=m /\
    (forall x, x\in s -> N x<=1) /\
    (forall r, size r=m -> (forall x, x\in r -> N x<=1) -> `|F r|<=`|F s|) /\
    (forall r, size r=m -> (forall x, x\in r -> N x<=1) -> `|F r|=`|F s| ->
      N (\sum_(x<-r) x)<=N (\sum_(x<-s) x)).
Proof.
have [u [hu [hmax hsum]]] := @finite_hilbert_form_secondary_maximum R V B hB n e he m f.
pose s : seq V := [seq u i | i<-enum 'I_m].
have hs : size s=m by rewrite /s size_map size_enum_ord.
have hsu : F s=f [tuple u i | i<m] := sform_wordsE f [tuple u i | i<m].
have hsn : (\sum_(x<-s) x)=\sum_i (u i : V) by rewrite /s big_map big_enum.
have hunit : forall x, x\in s -> N x<=1.
  move=> x /mapP[i hi ->]; exact: hu.
have hconvert r (hr : size r=m) : exists v : 'I_m -> inner_metric_space hB,
  (forall x, x\in r -> N x<=1) ->
  (forall i, N (v i)<=1) /\ F r=f [tuple v i | i<m] /\
  (\sum_(x<-r) x)=\sum_i (v i : V).
  have ht : size r==m := introT eqP hr.
  pose t : m.-tuple V := Tuple ht.
  exists (fun i=>tnth t i)=> hb.
  split; first by move=> i; apply: hb; exact: mem_tnth i t.
  split.
  - have htE : [tuple tnth t i | i<m]=t.
      by apply: eq_from_tnth=> i; rewrite tnth_mktuple.
    rewrite htE; exact: sform_wordsE f t.
  - exact (@big_tuple V 0 +%R V m t predT idfun).
exists s; split=> //; split=> //; split.
- move=> r hr hb; have [v hv] := hconvert r hr.
  have [hvu [hfv hsv]] := hv hb.
  rewrite hfv hsu; exact: hmax hvu.
- move=> r hr hb hf; have [v hv] := hconvert r hr.
  have [hvu [hfv hsv]] := hv hb.
  rewrite hfv hsu in hf; rewrite hsv hsn; exact: hsum hvu hf.
Qed.

(** Source for [hilbert_word_maximum_operator_bound]: Federer
    1.10.5, p. 48, supporting identification of a finite
    maximum on lists with an upper bound for the actual operator norm. *)
Lemma hilbert_word_maximum_operator_bound M :
  (forall s, size s=m -> (forall x, x\in s -> N x<=1) -> `|F s|<=M) ->
  (symmetric_operator_norm (W:=R^o) (proj1 (inner_norm_real_norm hB))
    (fun r:R=>(`|r|)%R) f <= M%:E)%E.
Proof.
move=> hb; apply: (proj2 (symmetric_operator_norm_bound (W:=R^o)
  (proj1 (inner_norm_real_norm hB)) (fun r:R=>`|r|) f M))=> t ht.
rewrite -(sform_wordsE f t); apply: hb; first exact: size_tuple.
move=> x /tnthP[i ->]; exact: ht.
Qed.

(** Source for [hilbert_positive_maximizer_unit_entries]: Federer
    1.10.5, p. 48, supporting saturation of every input
    constraint at a positive maximum. The homogeneous evaluation bound
    forces the product of the entry lengths, each at most one, to be one. *)
Lemma hilbert_positive_maximizer_unit_entries s : size s=m ->
  (forall x, x\in s -> N x<=1) -> 0<`|F s| ->
  (forall r, size r=m -> (forall x, x\in r -> N x<=1) -> `|F r|<=`|F s|) ->
  forall x, x\in s -> N x= 1.
Proof.
move=> hs hu hp hmax.
have hL := hilbert_word_maximum_operator_bound hmax.
have hb := @symmetric_form_word_norm_bound R V R^o N (fun r:R=>`|r|)
  (inner_norm_real_norm hB) (proj1 (scalar_absolute_value_norm R)) m f _ hL s hs.
apply: (@positive_product_maximizer_factors R V N s `|F s| hp) hb.
move=> x hx; apply/andP; split; [exact: inner_norm_nonnegative|exact: hu hx].
Qed.
End Maximum.
