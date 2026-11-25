(** Federer (1969), 3.4.5, p. 319: analytic germs
    use an actual analytic neighbourhood; values elsewhere are irrelevant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormClassZeroTopology NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticDomain NormAnalyticLocal NormAnalyticOperations NormAnalyticScalarProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_open_representative]: the real
    analytic functions at a in 3.4.5, p. 319, are
    analytic throughout some open neighbourhood of a contained in
    their original domain. This follows directly from 3.1.24(1). *)
Lemma analytic_germ_open_representative (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) (a:X):
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  exists U:set X,U a /\ U `<=` A /\ @open (real_norm_metric_space hNX) U /\
    @norm_analytic R X Y NX NY hNX hNY U f.
Proof.
move=>[U [c [ha [hUA [hClass hBound]]]]].
exists U;split;first exact:ha.
split;first exact:hUA.
split;first exact:(@norm_class_zero_domain_open R X Y NX NY hNX U f
  (norm_class_continuous (hClass 0%N))).
move=>x hx;exists U,c;split;first exact:hx.
split;first by move=>y hy.
by split.
Qed.

(** Source for [analytic_germ_product_at]: closure under
    functional multiplication in the ring of 3.4.5, p. 319.
    Choose common actual analytic neighbourhoods, then use the
    proved scalar product rule of 3.1.24. *)
Lemma analytic_germ_product_at (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A B:set X) (f g:X->R) (a:X):
  @norm_analytic_at R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) A f a ->
  @norm_analytic_at R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) B g a ->
  @norm_analytic_at R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    (A `&` B) (fun x=>f x*g x) a.
Proof.
move=>hF hG.
have [U [ha [hUA [hU hf]]]]:=analytic_germ_open_representative hF.
have [V [hb [hVB [hV hg]]]]:=analytic_germ_open_representative hG.
pose W:=U `&` V.
have hW:@open (real_norm_metric_space hNX) W:=openI hU hV.
have hOpen x (hx:W x):norm_domain_interior NX W x.
  have hNeighbourhood:=hW;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX W x).2 (hNeighbourhood x hx)).
have hfW:=@norm_analytic_open_restriction R X R^o NX (fun t=>`|t|)
  hNX (@scalar_absolute_value_norm R) U W f (fun x hx=>hx.1) hOpen hf.
have hgW:=@norm_analytic_open_restriction R X R^o NX (fun t=>`|t|)
  hNX (@scalar_absolute_value_norm R) V W g (fun x hx=>hx.2) hOpen hg.
have hProduct:=@norm_analytic_scalar_product R X NX hNX W f g hfW hgW.
apply:(@norm_analytic_at_domain_enlargement R X R^o NX (fun t=>`|t|)
  hNX (@scalar_absolute_value_norm R) W (A `&` B) (fun x=>f x*g x) a _ (hProduct a (conj ha hb))).
by move=>x [hx hy];split;[exact:hUA x hx|exact:hVB x hy].
Qed.
