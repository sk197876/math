(** Federer (1969), 4.1.12, pp. 367–368:
    extend T along Q(phi)=(phi,d phi) in the
    original product seminorm. This existence proof
    reuses Hahn–Banach. Its auxiliary graph and pair
    map remain inside the proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP RealSeminormOperations RealSeminormMaximum
  PartialLinearMap HahnBanach SeminormRealDualBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [seminorm_graph_pair_extension]: the original
    Hahn–Banach step yields a linear L on the product,
    agreeing with T on (phi,d phi) and bounded by
    c max(nu_K^0(phi),nu_K^0(psi)), Federer 4.1.12,
    pp. 367–368. The supporting statement uses supplied
    seminorms on arbitrary vector spaces. *)
Theorem seminorm_graph_pair_extension (R:realType) (E F:lmodType R)
    (p:E->R) (q:F->R) (hp:is_real_seminorm p) (hq:is_real_seminorm q)
    (d:Hom E F) (T:Hom E R^o) c:
  0<=c->(forall x,`|T x|<=c * Num.max (p x) (q (d x)))->
  exists L:Hom [the lmodType R of (E * F)%type] R^o,
    (forall x,L (x,d x)=T x) /\
    forall x y,`|L (x,y)|<=c * Num.max (p x) (q y).
Proof.
move=>hc hBound.
pose P:=[the lmodType R of (E * F)%type].
have hFirst:linear (fun z:P=>z.1) by move=>a x y;by [].
have hSecond:linear (fun z:P=>z.2) by move=>a x y;by [].
pose base:=fun z:P=>Num.max (p z.1) (q z.2).
have hBase:is_real_seminorm base.
  exact:(real_seminorm_maximum
    (@real_seminorm_linear_precompose R P E p hp (fun z=>z.1) hFirst)
    (@real_seminorm_linear_precompose R P F q hq (fun z=>z.2) hSecond)).
pose N:=fun z:P=>c * base z.
have hN:is_real_seminorm N:=real_seminorm_positive_multiple hBase hc.
have hQ:linear (fun x:E=>((x,d x):P)).
  move=>a x y;change ((a*:x+y,d (a*:x+y))=(a*:x+y,a*:d x+d y)).
  by rewrite (linearP d).
pose Q:Hom E P:=@HomMap R E P (fun x=>(x,d x)) (introT (asboolP _) hQ).
have hInjective:injective Q.
  move=>x y hEqual;have h:=congr1 (fun z:P=>z.1) hEqual.
  exact:h.
pose G:=fun z:P=>fun a:R^o=>exists x:E,Q x=z /\T x=a.
have hGraph:linear_graph G.
  split.
  - exists 0;split;exact:linear0.
  - split.
    + move=>x y u v [a [hQa hTa]] [b [hQb hTb]].
      exists (a+b);split;first by rewrite (linD (hom_linear Q)) hQa hQb.
      by rewrite (linD (hom_linear T)) hTa hTb.
    + split.
      * move=>a x u [b [hQb hTb]];exists (a*:b);split.
        -- by rewrite (linZ (hom_linear Q)) hQb.
        -- by rewrite (linZ (hom_linear T)) hTb.
      * move=>z a b [x [hQx hTx]] [y [hQy hTy]].
        have hxy:=hInjective x y (eq_trans hQx (esym hQy)).
        subst y;exact:(eq_trans (esym hTx) hTy).
have hDom:forall z a,G z a->a<=N z.
  move=>z a [x [hQx hTx]];rewrite -hQx -hTx.
  change (T x<=c * Num.max (p x) (q (d x))).
  exact:(le_trans (ler_norm (T x)) (hBound x)).
have [L [hAgreement hLBound]]:=@seminorm_hahn_banach R P N hN G hGraph hDom.
pose M:=hom_of_linear L.
have hM:forall z:P,`|M z|<=c * base z.
  apply:(@linear_one_sided_seminorm_bound_iff R P base hBase M c).1=>z.
  exact:hLBound z.
exists M;split.
- move=>x;change (L (Q x)=T x);apply:hAgreement.
  exists x;by split.
- move=>x y;exact:hM (x,y).
Qed.
