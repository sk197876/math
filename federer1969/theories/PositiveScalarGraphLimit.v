(** Federer (1969), 4.1.7, p. 357: uniqueness
    of the original partial scalar quotient limit.
    This adapter reuses the norm-limit uniqueness
    theorem of 4.1.4, p. 349. The original
    relation retains its domain of definedness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [positive_scalar_graph_limit]: the
    original positive-radius limit of a partial
    scalar relation, supporting Federer 4.1.7,
    p. 357. Each sufficiently small radius must
    have an actual value in the relation. *)
Definition positive_scalar_graph_limit (R:realType) (G:R->R->Prop) (l:R):Prop:=
  forall eta:R,0<eta->exists d:R,0<d /\forall r:R,0<r->r<d->
    exists q:R,G r q /\`|q-l|<eta.

(** Source for [positive_scalar_graph_limit_unique]:
    the original limit of a single-valued scalar
    relation is unique, supporting Federer 4.1.7,
    p. 357. A comparison function is chosen
    only inside the proof of uniqueness. *)
Theorem positive_scalar_graph_limit_unique (R:realType) (G:R->R->Prop)
    (hG:forall r a b,G r a->G r b->a=b) a b:
  positive_scalar_graph_limit G a->positive_scalar_graph_limit G b->a=b.
Proof.
move=>ha hb.
pose f (r:R):R:=match pselect (exists q:R,G r q) with
  |left h=>projT1 (cid h)
  |right _=>0
  end.
have hValue r q (hq:G r q):f r=q.
  rewrite /f;case:pselect=>[h|hn].
  - exact:(@hG r _ q (projT2 (cid h)) hq).
  - exact:False_ind _ (hn (ex_intro (fun t=>G r t) q hq)).
have hLimit l:positive_scalar_graph_limit G l->positive_norm_limit (fun t:R^o=>`|t|) f l.
  move=>hl eta hEta;have[d [hd hBound]]:=hl eta hEta.
  exists d;split=>//r hr hSmall.
  have[q [hq hError]]:=hBound r hr hSmall.
  by rewrite (@hValue r q hq).
exact:(@positive_norm_limit_unique R R^o (fun t:R^o=>`|t|) (@scalar_absolute_value_norm R)
  f a b (@hLimit a ha) (@hLimit b hb)).
Qed.
