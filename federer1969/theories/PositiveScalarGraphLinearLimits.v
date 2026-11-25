(** Federer (1969), 4.1.7, p. 357: linearity
    of the original scalar ball limits. The
    earlier positive-parameter linear limit laws of
    4.1.5 apply on the actual common domain.
    No value is assigned to an undefined quotient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP PositiveNormLimitUP PositiveRealLinearLimits
  PositiveScalarGraphLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_scalar_graph_limit_comparison]:
    a supporting comparison function for the
    original partial scalar limit in Federer
    4.1.7, p. 357. Its arbitrary values
    outside the graph are confined to this
    existence proof; the original domain is retained. *)
Lemma positive_scalar_graph_limit_comparison (R:realType) (G:R->R->Prop)
    (hG:forall r a b,G r a->G r b->a=b):
  exists f:R->R,(forall r q,G r q->f r=q) /\
    forall l,positive_scalar_graph_limit G l->
      positive_norm_limit (fun t:R^o=>`|t|) f l.
Proof.
pose f (r:R):R:=match pselect (exists q:R,G r q) with
  |left h=>projT1 (cid h)
  |right _=>0
  end.
have hValue r q (hq:G r q):f r=q.
  rewrite /f;case:pselect=>[h|hn].
  - exact:(@hG r _ q (projT2 (cid h)) hq).
  - exact:False_ind _ (hn (ex_intro (fun t=>G r t) q hq)).
exists f;split;first exact:hValue.
move=>l hl eta hEta;have[d [hd hBound]]:=hl eta hEta.
exists d;split=>//r hr hSmall.
have[q [hq hError]]:=hBound r hr hSmall.
by rewrite (@hValue r q hq).
Qed.

(** Source for [positive_scalar_graph_limit_linear]:
    sums and real scalar multiples of the
    original partial quotient limits, supporting
    Federer 4.1.7, p. 357. The proof
    takes a common positive-radius domain and
    reuses the proved scalar limit arithmetic. *)
Theorem positive_scalar_graph_limit_linear (R:realType)
    (G H J:R->R->Prop)
    (hG:forall r a b,G r a->G r b->a=b)
    (hH:forall r a b,H r a->H r b->a=b)
    (c:R)
    (hLinear:forall r a b,G r a->H r b->J r (c*a+b)) a b:
  positive_scalar_graph_limit G a->positive_scalar_graph_limit H b->
  positive_scalar_graph_limit J (c*a+b).
Proof.
move=>ha hb.
have[f [hF hFLimit]]:=positive_scalar_graph_limit_comparison hG.
have[g [hGValue hGLimit]]:=positive_scalar_graph_limit_comparison hH.
have hLimit:=@positive_real_limit_add R (fun r=>c*f r) g (c*a) b
  (@positive_real_limit_scale R f a c (@hFLimit a ha)) (@hGLimit b hb).
move=>eta hEta.
have[d [hd hBound]]:=hLimit eta hEta.
have[u [hu hU]]:=ha 1 ltr01.
have[v [hv hV]]:=hb 1 ltr01.
exists (Num.min d (Num.min u v));split.
- by rewrite !lt_min hd hu hv.
- move=>r hr hSmall.
  have/andP[hrd /andP[hru hrv]]:(r<d)&&((r<u)&&(r<v))
    by move:hSmall;rewrite !lt_min.
  have[p [hp _]]:=hU r hr hru.
  have[q [hq _]]:=hV r hr hrv.
  exists (c * p + q);split;first exact:(@hLinear r p q hp hq).
  rewrite -(@hF r p hp) -(@hGValue r q hq).
  exact:(hBound r hr hrd).
Qed.
