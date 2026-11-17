(** General topology supporting Federer (1969),
    3.4.8(11), p. 335: the inverse of
    an original component homeomorphism is continuous
    on its open base component. A total
    representative may be chosen without changing
    any value on that component. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_subset_continuous_extension_exists]:
    a local representative of the actual inverse
    component map in 3.4.8(11), p. 335.
    Its values away from the open component
    have no mathematical role. *)
Theorem open_subset_continuous_extension_exists (R:realType) (X Y:metricType R)
    (B:set Y) (F:metric_subset B->X) (x0:X):
  open B ->continuous F ->exists f:Y->X,
    (forall b:metric_subset B,f (val b) = F b) /\
    forall y,B y ->{for y,continuous f}.
Proof.
move=>hOpen hF.
pose f:=fun y:Y=>if pselect (B y) is left h then
  F (@exist Y (fun z=>z \in B) y (mem_set h)) else x0.
have hValue b:f (val b) = F b.
  rewrite /f;case:(pselect (B (val b)))=>hB.
  - congr (F _);apply:val_inj;by [].
  - exfalso;exact:hB (set_valP b).
exists f;split;first exact:hValue.
move=>y hBy W hW.
pose b:metric_subset B:=exist _ y (mem_set hBy).
have hAt:f y = F b:=hValue b.
have hWF:nbhs (F b) W by rewrite -hAt.
have hFNear:=hF b W hWF.
have [d hd hControl]:=proj1 (metricType_numDomainType.nbhs_mdistP b _) hFNear.
have hBNear:nbhs y B by move:hOpen;rewrite openE;exact.
have [r hr hInside]:=proj1 (metricType_numDomainType.nbhs_mdistP y B) hBNear.
apply:(proj2 (metricType_numDomainType.nbhs_mdistP y _)).
exists (Num.min r d);first by rewrite /= lt_min hr hd.
move=>z hz.
have /andP [hzR hzD]:(mdist y z<r) && (mdist y z<d) by rewrite -lt_min.
have hBz:=hInside z hzR.
pose c:metric_subset B:=exist _ z (mem_set hBz).
have hC:mdist b c<d:=hzD.
have hWC:=hControl c hC.
change (W (F c)) in hWC.
by rewrite -(hValue c) in hWC.
Qed.
