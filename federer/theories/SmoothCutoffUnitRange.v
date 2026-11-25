(** Federer (1969), 3.1.11, p. 223,
    and 4.1.1, pp. 344–345: apply the
    original smooth scalar unit cutoff to a
    compact smooth cutoff. This retains its
    support and neighbourhood plateau while ensuring
    values in [0,1], as needed in
    the first example of 4.1.12, p. 368. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormRegularity NormRegularityOperations
  ContinuousMultilinearSealed NormOpenDomainLaws CompactSupportFunctionUP SmoothCompactCutoffUP
  ScalarUnitCutoffUP ScalarUnitCutoffSealed ScalarUnitCutoffSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothCutoffUnitRange.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variables U K:set X.
Variable chi:X->R.
Hypothesis hChi:is_smooth_compact_cutoff hNX U K chi.
Local Notation hR := (@scalar_absolute_value_norm R).
Local Notation T := (real_norm_metric_space hNX).
Local Notation g := (@ScalarUnitCutoff.value R).
Local Notation hG := (@ScalarUnitCutoff.laws R).

(** Source for [smooth_cutoff_unit_range_exists]:
    a compact smooth cutoff can be replaced
    by one with values in [0,1], the
    same support bound and the same unit
    neighbourhood. This supports the bounded endpoint
    tests in Federer 4.1.12, p. 368,
    using only the preceding scalar cutoff laws. *)
Theorem smooth_cutoff_unit_range_exists:
  exists psi:X->R,is_smooth_compact_cutoff hNX U K psi /\
    (forall x,0<=psi x<=1) /\
    @real_function_support R T psi `<=` @real_function_support R T chi.
Proof.
pose psi x:=g (1-chi x).
have hGClass:norm_class_all_orders hR hR (fun _=>True) g.
  exact:(@scalar_unit_cutoff_class_infinity R
    (fun j=>@ContinuousMultilinear.space R j R^o R^o (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) hR hR)
    (fun j=>@ContinuousMultilinear.evaluation R j R^o R^o (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) hR hR)
    (fun j=>@ContinuousMultilinear.norm R j R^o R^o (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) hR hR)
    (fun j=>@ContinuousMultilinear.laws R j R^o R^o (fun t:R^o=>`|t|) (fun t:R^o=>`|t|) hR hR)).
have hClass:norm_class_all_orders hNX hR (fun _=>True) psi.
  move=>k.
  have hOne:=@norm_class_constant R X R^o NX (fun t:R^o=>`|t|) hNX hR
    (fun _=>True) 1 k (fun x _=>norm_full_domain_interior NX x).
  have hInput:=@norm_class_subtract R X R^o NX (fun t:R^o=>`|t|) hNX hR
    (fun _=>True) (fun _=>1) chi k hOne (smooth_cutoff_class hChi k).
  exact:(@norm_class_compose_on R X R^o R^o NX (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    hNX hR hR (fun _=>True) (fun _=>True) (fun x=>1-chi x) g k
    (fun _ _=>Logic.I) hInput (hGClass k)).
have hSupport:@real_function_support R T psi `<=` @real_function_support R T chi.
  apply:closureS=>x hNonzero.
  move=>hZero.
  apply:hNonzero;rewrite /psi hZero subr0.
  exact:(scalar_unit_cutoff_upper hG (lexx 1)).
exists psi;split.
- constructor.
  + exact:hClass.
  + refine (@subclosed_compact T (@real_function_support R T psi)
      (@real_function_support R T chi) (@real_function_support_closed R T psi)
      (smooth_cutoff_compact hChi) hSupport).
  + exact:subset_trans hSupport (smooth_cutoff_support_in_domain hChi).
  + have[W [hW [hKW hOne]]]:=smooth_cutoff_neighbourhood_plateau hChi.
    exists W;split;first exact:hW.
    split;first exact:hKW.
    move=>x hx;rewrite /psi (hOne x hx) subrr.
    exact:(scalar_unit_cutoff_lower hG (lexx 0)).
- split;first by move=>x;exact:(scalar_unit_cutoff_bounds hG (1-chi x)).
  exact:hSupport.
Qed.
End SmoothCutoffUnitRange.
