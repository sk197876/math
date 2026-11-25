(** Federer (1969), 4.1.5, p. 350:
    the final weak compactness argument uses
    the cartesian product of finite evaluation
    intervals. Tychonoff is general topology;
    linearity and the original pointwise bounds
    are closed finite-coordinate conditions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology normedtype lra.
From Federer Require Import Hom DaniellSpaceCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_linear_product_set]: the real
    linear evaluation functions satisfying the
    printed pointwise bounds in Federer 4.1.5,
    p. 350, in their product topology. *)
Definition bounded_linear_product_set (R:realType) (E:lmodType R) (B:E->R):
    set (prod_topology (fun _:E=>R)):=
  [set a|linear (fun x:E=>(a x:R^o)) /\forall x:E,a x<=B x].

(** Source for [bounded_linear_product_closed]: linearity
    and the original evaluation inequalities
    are closed in the full product,
    supporting Federer 4.1.5, p. 350. *)
Theorem bounded_linear_product_closed (R:realType) (E:lmodType R) (B:E->R):
  closed (@bounded_linear_product_set R E B).
Proof.
move=>a hClosure; split.
- move=>c u v.
  have hUpper f:@bounded_linear_product_set R E B f ->
      \sum_(p <- [::(1,c*:u+v);(-c,u);(-1,v)]) p.1*f p.2<=0.
    move=>[hLinear _]; have h:=hLinear c u v.
    change (f (c*:u+v)=c*f u+f v) in h.
    rewrite !big_cons big_nil /=; nra.
  have hLower f:@bounded_linear_product_set R E B f ->
      \sum_(p <- [::(-1,c*:u+v);(c,u);(1,v)]) p.1*f p.2<=0.
    move=>[hLinear _]; have h:=hLinear c u v.
    change (f (c*:u+v)=c*f u+f v) in h.
    rewrite !big_cons big_nil /=; nra.
  have hOne:=product_closure_linear_le hClosure hUpper.
  have hTwo:=product_closure_linear_le hClosure hLower.
  rewrite !big_cons big_nil /= in hOne hTwo.
  change (a (c*:u+v)=c*a u+a v); nra.
- move=>u.
  have hBound f:@bounded_linear_product_set R E B f ->
      \sum_(p <- [::(1,u)]) p.1*f p.2<=B u.
    move=>[_ hB]; by rewrite !big_cons big_nil /= mul1r addr0; exact:hB.
  have h:=product_closure_linear_le hClosure hBound.
  by rewrite !big_cons big_nil /= mul1r addr0 in h.
Qed.

(** Source for [bounded_linear_product_compact]: the bounded
    real linear evaluation set is compact,
    by the same product-of-intervals argument
    as Federer 4.1.5, p. 350. The
    bound B may be nonhomogeneous. *)
Theorem bounded_linear_product_compact (R:realType) (E:lmodType R) (B:E->R):
  compact (@bounded_linear_product_set R E B).
Proof.
pose C:=fun x:E=>Num.max (B x) (B (-x)).
pose T:set (prod_topology (fun _:E=>R)):=[set a|forall x:E,`|a x|<=C x].
have hCompact:compact T.
  have h:=@tychonoff E (fun _=>R) (fun x=>[set t:R | `|t|<=C x]).
  apply:h=>x.
  have hSet:[set t:R | `|t|<=C x]=`[-C x,C x].
    by apply/seteqP; split=>t /=; rewrite in_itv /= ler_norml.
  rewrite hSet; exact:segment_compact.
apply:(subclosed_compact (@bounded_linear_product_closed R E B) hCompact)=>a [hLinear hPoint] u.
have hZero:a 0=0.
  have h:=hLinear 1 0 0.
  change (a (1*:0+0)= 1*a 0+a 0) in h.
  rewrite scale1r addr0 mul1r in h; lra.
have hNeg:a (-u)= -a u.
  have h:=hLinear (-1) u 0.
  change (a ((-1)*:u+0)=(-1)*a u+a 0) in h.
  by rewrite addr0 scaleN1r hZero mulN1r addr0 in h.
have hUpper:a u<=C u.
  apply:le_trans (hPoint u) _; by rewrite /C le_max lexx.
have hLower: -a u<=C u.
  rewrite -hNeg; apply:le_trans (hPoint (-u)) _; by rewrite /C le_max lexx orbT.
rewrite ler_norml; apply/andP; split=>//; by rewrite lerNl.
Qed.
